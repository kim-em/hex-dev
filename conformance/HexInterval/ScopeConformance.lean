/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PackageRegistry
import HexInterval.Experiment.Policy

/-!
# Arbitrary-scope propagator conformance

These canaries exercise a package-owned contractor whose declared reads and
writes are not slots of one head operation.  The fact domain is a tiny `Nat`
order so the tests isolate binding, scheduling, and atomicity from interval
endpoint arithmetic.  None of these checks use `native_decide`.
-/

namespace Hex.Interval.ScopeConformance

open Experiment.Propagator

abbrev Rank := Nat

def rankDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "scope.source" }
def unaryKey : OpKey := { name := "scope.unary" }
def relationKey : OpKey := { name := "scope.relation" }

def scopedKey : RuleKey := { name := "scope.contract" }
def localKey : RuleKey := { name := "scope.local" }

def node (index : Nat) : NodeId := { index }

def sourceNode : Node :=
  { domain := real, op := { index := 0 }, args := [] }

def unaryNode (input : Nat) : Node :=
  { domain := real, op := { index := 1 }, args := [node input] }

def relationNode (left right : Nat) : Node :=
  { domain := real, op := { index := 2 }, args := [node left, node right] }

def operations : Array Operation :=
  #[{ key := sourceKey, inputs := [], output := real },
    { key := unaryKey, inputs := [real], output := real },
    { key := relationKey, inputs := [real, real], output := real }]

/-- Nodes 0 and 1 are inputs, 2 and 3 are independently located outputs,
node 4 is the structural anchor, and node 5 is deliberately unrelated. -/
def program : Program :=
  { operations
    nodes :=
      #[sourceNode, sourceNode, unaryNode 0, unaryNode 1, relationNode 0 1,
        sourceNode] }

def extendedProgram : Program :=
  { program with nodes := program.nodes.push (unaryNode 2) }

def scopedRule : Registration :=
  { key := scopedKey
    head := relationKey
    kind := .improve
    watches := []
    writes := []
    binding := .scoped }

def localRule : Registration :=
  { key := localKey
    head := unaryKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

/-- Including the output nodes in `watches` asks for local contractor closure:
an improvement wakes this application again, and queue coalescing turns two
changed outputs into one revisit. -/
def scope : ScopeBinding :=
  { rule := scopedKey
    anchor := node 4
    watches := [node 0, node 1, node 2, node 3]
    writes := [node 2, node 3] }

def writeOnlyScope : ScopeBinding :=
  { scope with watches := [node 0, node 1] }

def limits : Limits :=
  { maxOperations := 8
    maxNodes := 16
    maxRules := 8
    maxArity := 4
    maxScopeNodes := 16
    maxApplications := 16
    maxQueueEntries := 16
    maxActions := 16
    maxAcceptedFacts := 16
    maxRetainedSuggestions := 4
    maxEffort := 4
    maxObservationValue := 32
    maxDiagnosticValue := 512
    maxOutcomeCandidates := 4
    maxOutcomeSuggestions := 2
    maxProposalItems := 4
    maxInstances := 2
    maxGeneration := 2
    maxNodeDepth := 16
    maxEqualities := 2
    splitEndpointLimit :=
      { maxEndpointHeight := 16
        maxAlignmentShift := 8 } }

def scopedOutcome (request : RuleRequest Rank) : Outcome Rank :=
  if request.inputs.map (fun input => input.node) != scope.watches ||
      request.writes != scope.writes then
    .failed 7
  else match request.inputs, request.writes with
  | [left, right, _, _], [leftTarget, rightTarget] =>
      let improvement := Nat.min left.fact right.fact
      .success
        [{ node := leftTarget, fact := improvement, payload := { index := 0 } },
          { node := rightTarget, fact := improvement, payload := { index := 1 } }]
        [] { visitedEntries := 4 }
  | _, _ => .failed 8

def writeOnlyOutcome (request : RuleRequest Rank) : Outcome Rank :=
  if request.inputs.map (fun input => input.node) != writeOnlyScope.watches ||
      request.writes != writeOnlyScope.writes then
    .failed 9
  else match request.inputs, request.writes with
  | [left, right], [leftTarget, rightTarget] =>
      let improvement := Nat.min left.fact right.fact
      .success
        [{ node := leftTarget, fact := improvement, payload := { index := 4 } },
          { node := rightTarget, fact := improvement, payload := { index := 5 } }]
        [] { visitedEntries := 2 }
  | _, _ => .failed 10

def scopedInvoke (calls : Nat) (request : RuleRequest Rank) : Outcome Rank × Nat :=
  (scopedOutcome request, calls + 1)

def writeOnlyInvoke (calls : Nat) (request : RuleRequest Rank) : Outcome Rank × Nat :=
  (writeOnlyOutcome request, calls + 1)

def scopedPackage : Package Rank :=
  { Cache := Nat
    cache := 0
    operations
    handlers :=
      #[{ registration := scopedRule
          invoke := scopedInvoke
          acceptsScope := fun actualProgram binding =>
            actualProgram.check && binding.same scope }] }

def run? : Option (RunResult Rank (Registry Rank)) :=
  match Registry.buildWithin limits #[scopedPackage] with
  | .error _ => none
  | .ok registry =>
      if !registry.acceptsProgram program || !registry.acceptsLimits program limits ||
          !registry.acceptsBindings program #[scope] then
        none
      else
        match Engine.start rankDomain program registry.registrations
            #[4, 6, 0, 0, 0, 9] limits #[scope]
              (Registry.acceptsBinding registry) with
        | .error _ => none
        | .ok state => some (drive Registry.invoke 4 state registry)

#guard program.check
#guard extendedProgram.check

-- The generic engine regards port order as opaque semantic data.  The owning
-- package accepts its matcher-produced order and vetoes a structurally valid
-- but semantically different projection.
#guard
  match Registry.buildWithin limits #[scopedPackage] with
  | .error _ => false
  | .ok registry =>
      registry.acceptsBindings program #[scope] &&
        !registry.acceptsBindings program
          #[{ scope with watches := scope.watches.reverse }] &&
        (match Engine.start rankDomain program registry.registrations
            #[4, 6, 0, 0, 0, 9] limits
              #[{ scope with watches := scope.watches.reverse }]
              (Registry.acceptsBinding registry) with
          | .error .invalidBindings => true
          | _ => false)

-- The package callback receives four nonlocal reads, owns two nonlocal writes,
-- and revisits exactly once after the atomic pair improves.
#guard
  match run? with
  | some result =>
      result.stop == .saturated && result.state.facts.toList == [4, 6, 4, 4, 0, 9] &&
        result.state.history.size == 2 && result.state.metrics.requests == 2 &&
        result.state.metrics.improvements == 2 &&
        result.state.metrics.queueInsertions == 2 &&
        result.state.metrics.suppressedInsertions == 1 &&
        result.cache.packages[0]?.any (fun package => package.invocations == 2)
  | none => false

def writeOnlyRun? : Option (RunResult Rank Nat) := do
  let state <- match Engine.start rankDomain program #[scopedRule]
      #[4, 6, 0, 0, 0, 9] limits #[writeOnlyScope] with
    | .ok state => some state
    | .error _ => none
  pure (drive writeOnlyInvoke 3 state 0)

-- Write authorization does not implicitly add a dependency.  With neither
-- output watched, the contractor runs once and remains asleep after its pair
-- of improvements.
#guard
  match writeOnlyRun? with
  | some result =>
      result.stop == .saturated && result.cache == 1 &&
        result.state.facts.toList == [4, 6, 4, 4, 0, 9] &&
        result.state.metrics.requests == 1 && result.state.metrics.improvements == 2 &&
        result.state.metrics.queueInsertions == 1
  | none => false

-- Waking an unrelated expression leaves a saturated scoped contractor asleep.
#guard
  match run? with
  | some result =>
      match result.state.wakeNode (node 5) with
      | .ok state =>
          state.queue.size == result.state.queue.size &&
            state.metrics.queueInsertions == result.state.metrics.queueInsertions
      | .error _ => false
  | none => false

def firstRequest? (customLimits : Limits := limits) :
    Option (RuleRequest Rank × Engine Rank) := do
  let state <- match Engine.start rankDomain program #[scopedRule]
      #[4, 6, 0, 0, 0, 9] customLimits #[scope] with
    | .ok state => some state
    | .error _ => none
  match state.poll with
  | .request request awaiting => some (request, awaiting)
  | _ => none

def revisitRequest? : Option (RuleRequest Rank) := do
  let (request, awaiting) <- firstRequest?
  let next <- match awaiting.submit (request.action.reply (scopedOutcome request)) with
    | .accepted _ state => some state
    | _ => none
  match next.poll with
  | .request request _ => some request
  | _ => none

-- The self-revisit observes the complete pair, never an intermediate state.
#guard
  match revisitRequest? with
  | some request =>
      request.fact? (node 2) == some 4 && request.fact? (node 3) == some 4 &&
        request.action.inputs ==
          [{ node := node 0, version := 0 }, { node := node 1, version := 0 },
            { node := node 2, version := 1 }, { node := node 3, version := 1 }]
  | none => false

-- A short history budget rolls both writes back.
#guard
  match firstRequest? { limits with maxAcceptedFacts := 1 } with
  | some (request, awaiting) =>
      match awaiting.submit (request.action.reply (scopedOutcome request)) with
      | .resourceLimit .acceptedFacts state =>
          state.facts.toList == [4, 6, 0, 0, 0, 9] && state.history.isEmpty
      | _ => false
  | none => false

-- A failed self-wakeup also rolls both writes back.
#guard
  match firstRequest? { limits with maxQueueEntries := 1 } with
  | some (request, awaiting) =>
      match awaiting.submit (request.action.reply (scopedOutcome request)) with
      | .resourceLimit .queueEntries state =>
          state.facts.toList == [4, 6, 0, 0, 0, 9] && state.history.isEmpty
      | _ => false
  | none => false

-- Reply admission still rejects any target outside the binding's write set.
#guard
  match firstRequest? with
  | some (request, awaiting) =>
      let outcome : Outcome Rank :=
        .success [{ node := node 5, fact := 4, payload := { index := 3 } }] [] {}
      match awaiting.submit (request.action.reply outcome) with
      | .invalid (.undeclaredWrite target) state =>
          target == node 5 && state.facts.toList == [4, 6, 0, 0, 0, 9]
      | _ => false
  | none => false

-- Scoped applications are compiled first.  Consequently later local
-- applications append after every old application when the program grows.
#guard
  match compileApplications program #[localRule, scopedRule] #[scope],
      compileApplications extendedProgram #[localRule, scopedRule] #[scope] with
  | some old, some new =>
      old.size == 3 && new.size == 4 && applicationsPrefix old new &&
        old[0]?.any (fun application =>
          application.rule.index == 1 && application.node == node 4 &&
            application.watches == scope.watches && application.writes == scope.writes) &&
        new[3]?.any (fun application =>
          application.rule.index == 0 && application.node == node 6)
  | _, _ => false

-- Port order is semantic package data: a different ordered projection is a
-- distinct application rather than a duplicate binding.
#guard
  match compileApplications program #[scopedRule]
      #[scope, { scope with watches := scope.watches.reverse }] with
  | some applications => applications.size == 2
  | none => false

def appendProposal : InstantiationRequest :=
  { key := 17
    nodes :=
      [{ domain := real
         op := { index := 1 }
         args := [.existing (node 2)] }]
    equalities := []
    payload := { index := 6 } }

def acceptsSixNodeScope (actualProgram : Program) (_ : ScopeBinding) : Bool :=
  actualProgram.nodes.size == 6

-- Installed package scopes are revalidated against a proposed final program.
-- A non-append-monotone package predicate therefore vetoes the whole extension
-- before it can enter retained state.
#guard
  match Engine.start rankDomain program #[localRule, scopedRule]
      #[4, 6, 0, 0, 0, 9] limits #[scope] acceptsSixNodeScope with
  | .error _ => false
  | .ok state =>
      match state.poll with
      | .request request awaiting =>
          match awaiting.submit
              (request.action.reply (.success [] [.instantiate appendProposal] {})) with
          | .invalid .malformedProposal next =>
              next.program.nodes.size == 6 && next.bindings.size == 1 &&
                next.suggestions.isEmpty && next.instanceHistory.isEmpty
          | _ => false
      | _ => false

def admittedAppend? : Option (Engine Rank) := do
  let state <- match Engine.start rankDomain program #[localRule, scopedRule]
      #[4, 6, 0, 0, 0, 9] limits #[scope] with
    | .ok state => some state
    | .error _ => none
  let (request, awaiting) <- match state.poll with
    | .request request awaiting => some (request, awaiting)
    | _ => none
  let retained <- match awaiting.submit
      (request.action.reply (.success [] [.instantiate appendProposal] {})) with
    | .accepted _ state => some state
    | _ => none
  match retained.admitInstantiation { index := 0 } with
  | .admitted [fresh] state => if fresh == node 6 then some state else none
  | _ => none

-- Actual program extension retains all three old application IDs and queue
-- bits, then appends the new local application and its work item.
#guard
  match admittedAppend? with
  | some state =>
      state.program.nodes.size == 7 && state.applications.size == 4 &&
        state.bindings.size == 1 && state.queued.toList == [false, true, true, true] &&
        state.queueHead == 1 && state.queue.size == 4 &&
        state.applications[0]?.any (fun application =>
          application.rule.index == 1 && application.node == node 4 &&
            application.watches == scope.watches && application.writes == scope.writes) &&
        state.applications[3]?.any (fun application =>
          application.rule.index == 0 && application.node == node 6)
  | none => false

/-! # Dynamically instantiated scopes -/

def dynamicKey : RuleKey := { name := "scope.dynamic" }

def dynamicRule : Registration :=
  { key := dynamicKey
    head := unaryKey
    kind := .improve
    watches := []
    writes := []
    binding := .scoped }

def proposedDynamicScope : ProposedScope :=
  { rule := dynamicKey
    anchor := .proposed 0
    watches := [.existing (node 0), .existing (node 1), .proposed 0]
    writes := [.proposed 0] }

/-- The same scope occurs twice deliberately.  Admission preserves both
output references while appending only one concrete application. -/
def dynamicRequest : InstantiationRequest :=
  { key := 23
    nodes :=
      [{ domain := real
         op := { index := 1 }
         args := [.existing (node 5)] }]
    equalities := []
    scopes := [proposedDynamicScope, proposedDynamicScope]
    payload := { index := 7 } }

def retainedDynamic? (customLimits : Limits := limits) : Option (Engine Rank) := do
  let state <- match Engine.start rankDomain program
      #[localRule, scopedRule, dynamicRule] #[4, 6, 0, 0, 0, 9]
      customLimits #[scope] with
    | .ok state => some state
    | .error _ => none
  let (request, awaiting) <- match state.poll with
    | .request request awaiting => some (request, awaiting)
    | _ => none
  match awaiting.submit
      (request.action.reply (.success [] [.instantiate dynamicRequest] {})) with
  | .accepted _ state => some state
  | _ => none

def admittedDynamic? (customLimits : Limits := limits) : Option (Engine Rank) := do
  let state <- retainedDynamic? customLimits
  match state.admitInstantiation { index := 0 } with
  | .admitted [fresh] state => if fresh == node 6 then some state else none
  | _ => none

-- New scopes append before the local applications generated by the same
-- event.  All older applications and dirty bits retain their exact indices.
#guard
  match admittedDynamic? with
  | some state =>
      state.program.nodes.size == 7 && state.programVersion == 1 &&
        state.applications.size == 5 && state.bindings.size == 2 &&
        state.queued.toList == [false, true, true, true, true] &&
        state.metrics.generatedNodes == 1 && state.metrics.generatedScopes == 1 &&
        state.instanceHistory[0]?.any (fun event =>
          event.products == [node 6] && event.newNodes == [node 6] &&
            event.bindings.length == 2 && event.newBindings.length == 1 &&
            event.applications == [{ index := 3 }, { index := 3 }] &&
            event.newApplications == [{ index := 3 }]) &&
        state.applications[3]?.any (fun application =>
          application.rule.index == 2 && application.node == node 6 &&
            application.watches == [node 0, node 1, node 6] &&
            application.writes == [node 6]) &&
        state.applications[4]?.any (fun application =>
          application.rule.index == 0 && application.node == node 6)
  | none => false

def dynamicOutcome (request : RuleRequest Rank) : Outcome Rank :=
  if request.inputs.map (fun input => input.node) != [node 0, node 1, node 6] ||
      request.writes != [node 6] then
    .failed 11
  else
    match request.inputs, request.writes with
    | left :: right :: _, [target] =>
        .success
          [{ node := target
             fact := Nat.min left.fact right.fact
             payload := { index := 8 } }]
          [] { visitedEntries := 3 }
    | _, _ => .failed 12

def dynamicInvoke (calls : List String) (request : RuleRequest Rank) :
    Outcome Rank × List String :=
  let calls := request.action.key.name :: calls
  if request.action.key == dynamicKey then (dynamicOutcome request, calls)
  else (.noChange {}, calls)

def dynamicFinal? : Option (RunResult Rank (List String)) := do
  let state <- admittedDynamic?
  pure (drive dynamicInvoke 12 state [])

-- The newly installed arbitrary-scope application is live immediately and
-- participates in ordinary self-revisit closure.
#guard
  match dynamicFinal? with
  | some result =>
      result.stop == .saturated && result.state.facts[6]? == some 4 &&
        result.cache.count dynamicKey.name == 2
  | none => false

def existingDynamicScope : ProposedScope :=
  { rule := dynamicKey
    anchor := .existing (node 2)
    watches := [.existing (node 0), .existing (node 1), .existing (node 2)]
    writes := [.existing (node 2)] }

def scopeOnlyRequest : InstantiationRequest :=
  { key := 29
    nodes := []
    equalities := []
    scopes := [existingDynamicScope, existingDynamicScope]
    payload := { index := 9 } }

def scopeOnlyInitial? (customLimits : Limits := limits) : Option (Engine Rank) := do
  let state <- match Engine.start rankDomain program
      #[localRule, scopedRule, dynamicRule] #[4, 6, 0, 0, 0, 9]
      customLimits #[scope] with
    | .ok state => some state
    | .error _ => none
  let (request, awaiting) <- match state.poll with
    | .request request awaiting => some (request, awaiting)
    | _ => none
  match awaiting.submit
      (request.action.reply (.success [] [.instantiate scopeOnlyRequest] {})) with
  | .accepted _ state => some state
  | _ => none

def scopeOnlyAdmitted? (customLimits : Limits := limits) :
    Option (Engine Rank × SuggestionId) := do
  let state <- scopeOnlyInitial? customLimits
  let selected : SuggestionId := { index := 0 }
  match state.admitInstantiation selected with
  | .admitted [] state => some (state, selected)
  | _ => none

-- Adding only a contractor application is a real network extension, despite
-- adding no expression node or equality.
#guard
  match scopeOnlyAdmitted? with
  | some (state, _) =>
      state.program.nodes.size == 6 && state.programVersion == 1 &&
        state.applications.size == 4 && state.bindings.size == 2 &&
        state.metrics.admittedInstances == 1 && state.metrics.generatedNodes == 0 &&
        state.metrics.generatedScopes == 1 &&
        (state.applications.toList.take 3).all (fun application =>
          application.generation == 0) &&
        state.applications[3]?.any (fun application => application.generation == 1) &&
        state.instanceHistory[0]?.any (fun event =>
          event.newNodes.isEmpty && event.bindings.length == 2 &&
            event.newBindings.length == 1 &&
            event.applications == [{ index := 3 }, { index := 3 }] &&
            event.newApplications == [{ index := 3 }])
  | none => false

def scopePolicyLimits : Policy.Limits :=
  { maxDecisions := 4
    maxTraversal := 64
    maxLiveOffers := 16 }

-- Scope-only admission consumes theorem-instantiation generation even though
-- it appends no node.  The policy budget view must report that consumption.
#guard
  match scopeOnlyAdmitted? with
  | some (engine, _) =>
      match (Policy.State.start engine scopePolicyLimits).view with
      | .ok (view, _) => view.remaining.generation == 1
      | .error _ => false
  | none => false

-- Traversal accounting includes variable scoped reads and retained scope
-- proposals.  The bounded scan fails as soon as its remaining allowance is
-- exhausted; the exact complete view costs 22 semantic items here.
#guard
  match scopeOnlyAdmitted? with
  | some (engine, _) =>
      match (Policy.State.start engine
          { scopePolicyLimits with maxTraversal := 5 }).view with
      | .error .traversalLimit => true
      | _ => false
  | none => false

#guard
  match scopeOnlyAdmitted? with
  | some (engine, _) =>
      match (Policy.State.start engine
          { scopePolicyLimits with maxTraversal := 21 }).view with
      | .error .traversalLimit => true
      | _ => false
  | none => false

#guard
  match scopeOnlyAdmitted? with
  | some (engine, _) =>
      match (Policy.State.start engine
          { scopePolicyLimits with maxTraversal := 22 }).view with
      | .ok (_, next) => next.metrics.traversal == 22
      | .error _ => false
  | none => false

-- Selecting the same scope-only proposal again allocates no second binding.
#guard
  match scopeOnlyAdmitted? with
  | some (state, selected) =>
      match state.admitInstantiation selected with
      | .duplicate next =>
          next.applications.size == 4 && next.bindings.size == 2 &&
            next.metrics.duplicateInstances == 1
      | _ => false
  | none => false

-- Application and queue limits roll back the node and scope together.
#guard
  match retainedDynamic? { limits with maxApplications := 3 } with
  | some state =>
      match state.admitInstantiation { index := 0 } with
      | .resourceLimit .applications next =>
          next.program.nodes.size == 6 && next.applications.size == 3 &&
            next.bindings.size == 1 && next.instanceHistory.isEmpty
      | _ => false
  | none => false

-- The fresh scope can fit while the local application induced by its new node
-- is the one which crosses the application cap.
#guard
  match retainedDynamic? { limits with maxApplications := 4 } with
  | some state =>
      match state.admitInstantiation { index := 0 } with
      | .resourceLimit .applications next =>
          next.program.nodes.size == 6 && next.applications.size == 3 &&
            next.bindings.size == 1 && next.instanceHistory.isEmpty
      | _ => false
  | none => false

#guard
  match admittedDynamic? { limits with maxApplications := 5 } with
  | some state => state.applications.size == 5 && state.program.nodes.size == 7
  | none => false

#guard
  match retainedDynamic? { limits with maxQueueEntries := 3 } with
  | some state =>
      match state.admitInstantiation { index := 0 } with
      | .resourceLimit .queueEntries next =>
          next.program.nodes.size == 6 && next.applications.size == 3 &&
            next.bindings.size == 1 && next.instanceHistory.isEmpty
      | _ => false
  | none => false

#guard
  match retainedDynamic? { limits with maxQueueEntries := 4 } with
  | some state =>
      match state.admitInstantiation { index := 0 } with
      | .resourceLimit .queueEntries next =>
          next.queue.size == 3 && next.applications.size == 3 &&
            next.instanceHistory.isEmpty
      | _ => false
  | none => false

#guard
  match admittedDynamic? { limits with maxQueueEntries := 5 } with
  | some state => state.queue.size == 5 && state.applications.size == 5
  | none => false

def scopeBoundaryRequest (watches : List NodeRef) : InstantiationRequest :=
  { key := 47
    nodes := []
    equalities := []
    scopes :=
      [{ rule := dynamicKey
         anchor := .existing (node 2)
         watches
         writes := [] }]
    payload := { index := 14 } }

def scopeBoundaryReply (watches : List NodeRef) : Option (ReplyResult Rank) := do
  let state <- match Engine.start rankDomain program
      #[localRule, scopedRule, dynamicRule] #[4, 6, 0, 0, 0, 9]
      { limits with maxScopeNodes := 4 } #[scope] with
    | .ok state => some state
    | .error _ => none
  let (request, awaiting) <- match state.poll with
    | .request request awaiting => some (request, awaiting)
    | _ => none
  pure <| awaiting.submit
    (request.action.reply (.success [] [.instantiate (scopeBoundaryRequest watches)] {}))

-- Arbitrary ports have their own exact per-scope bound, independent of local
-- operation arity.
#guard
  match scopeBoundaryReply
      [.existing (node 0), .existing (node 1), .existing (node 2), .existing (node 3)] with
  | some (.accepted plan state) => plan.kept.length == 1 && state.suggestions.size == 1
  | _ => false

#guard
  match scopeBoundaryReply
      [.existing (node 0), .existing (node 1), .existing (node 2),
        .existing (node 3), .existing (node 5)] with
  | some (.invalid .oversizedProposal state) => state.suggestions.isEmpty
  | _ => false

def malformedScopeRequest : InstantiationRequest :=
  { scopeOnlyRequest with
    scopes := [{ existingDynamicScope with watches := [.existing (node 0), .existing (node 0)] }] }

def rejectDynamicScope (_ : Program) (binding : ScopeBinding) : Bool :=
  binding.rule != dynamicKey

-- A malformed dynamic scope is rejected before it can enter retained policy
-- state, not deferred until selection.
#guard
  match Engine.start rankDomain program #[localRule, scopedRule, dynamicRule]
      #[4, 6, 0, 0, 0, 9] limits #[scope] with
  | .error _ => false
  | .ok state =>
      match state.poll with
      | .request request awaiting =>
          match awaiting.submit
              (request.action.reply
                (.success [] [.instantiate malformedScopeRequest] {})) with
          | .invalid .malformedProposal next =>
              next.suggestions.isEmpty && next.bindings.size == 1
          | _ => false
      | _ => false

-- Session-supplied package validation runs before retention as well as before
-- commit.  Thus one package cannot use a structurally valid proposal to install
-- an arbitrary port projection for a rule whose owner vetoes that scope.
#guard
  match Engine.start rankDomain program #[localRule, scopedRule, dynamicRule]
      #[4, 6, 0, 0, 0, 9] limits #[scope] rejectDynamicScope with
  | .error _ => false
  | .ok state =>
      match state.poll with
      | .request request awaiting =>
          match awaiting.submit
              (request.action.reply (.success [] [.instantiate scopeOnlyRequest] {})) with
          | .invalid .malformedProposal next =>
              next.suggestions.isEmpty && next.bindings.size == 1
          | _ => false
      | _ => false

/-- Consume ordinary queued work until the dynamically installed scope is
invoked.  Returning the post-reply state lets the test below retain that exact
generation-one action as causal provenance for another proposal. -/
def nextDynamicAction? : Nat -> Engine Rank -> Option (Engine Rank × Action)
  | 0, _ => none
  | fuel + 1, state =>
      match state.poll with
      | .request request awaiting =>
          match awaiting.submit (request.action.reply (.noChange {})) with
          | .accepted _ next =>
              if request.action.key == dynamicKey then
                some (next, request.action)
              else
                nextDynamicAction? fuel next
          | _ => none
      | _ => none

def generationChain? : Option (Engine Rank × Action) := do
  let (state, _) <- scopeOnlyAdmitted? { limits with maxGeneration := 1 }
  nextDynamicAction? 4 state

def chainedScopeRequest : InstantiationRequest :=
  { key := 41
    nodes := []
    equalities := []
    scopes :=
      [{ rule := dynamicKey
         anchor := .existing (node 3)
         watches := [.existing (node 0)]
         writes := [] }]
    payload := { index := 12 } }

-- Causality follows the application which emitted a proposal, even when its
-- new scope mentions only generation-zero nodes.  Otherwise a chain of
-- scope-only instantiations could evade `maxGeneration` forever.
#guard
  match generationChain? with
  | some (state, action) =>
      let retained : RetainedSuggestion :=
        { action
          suggestion := .instantiate chainedScopeRequest
          splitVersion := none }
      action.generation == 1 &&
        !state.actionFresh { action with generation := 0 } &&
        state.instantiationGeneration? retained == some 2 &&
        match state.admitRetained retained with
        | .resourceLimit .generation next =>
            next.programVersion == state.programVersion &&
              next.applications.size == state.applications.size &&
              next.bindings.size == state.bindings.size &&
              next.instanceHistory.size == state.instanceHistory.size
        | _ => false
  | none => false

def secondDynamicRequest : InstantiationRequest :=
  { key := 43
    nodes :=
      [{ domain := real
         op := { index := 1 }
         args := [.existing (node 2)] }]
    equalities := []
    scopes :=
      [{ rule := dynamicKey
         anchor := .existing (node 6)
         watches := [.existing (node 0), .existing (node 1), .existing (node 6)]
         writes := [.existing (node 6)] },
        { rule := dynamicKey
          anchor := .proposed 0
          watches := [.existing (node 0), .proposed 0]
          writes := [.proposed 0] },
        { rule := dynamicKey
          anchor := .proposed 0
          watches := [.existing (node 0), .proposed 0]
          writes := [.proposed 0] }]
    payload := { index := 13 } }

def admittedDynamicTwice? : Option (Engine Rank × Engine Rank) := do
  let first <- admittedDynamic?
  let (ready, action) <- nextDynamicAction? 4 first
  let retained : RetainedSuggestion :=
    { action
      suggestion := .instantiate secondDynamicRequest
      splitVersion := none }
  match ready.admitRetained retained with
  | .admitted [fresh] next =>
      if fresh == node 7 then some (ready, next) else none
  | _ => none

def listSubsequence [DecidableEq alpha] (old new : List alpha) : Bool :=
  match old, new with
  | [], _ => true
  | _ :: _, [] => false
  | previous :: old, current :: new =>
      if previous == current then listSubsequence old new
      else listSubsequence (previous :: old) new
termination_by old.length + new.length

def watcherSubsequences (old new : Array (List WorkItem)) : Bool := Id.run do
  if new.size < old.size then return false
  for index in [0:old.size] do
    match old[index]?, new[index]? with
    | some previous, some current =>
        if !listSubsequence previous current then return false
    | _, _ => return false
  return true

-- A second admission interleaves another arbitrary scope with the local rule
-- generated for its new expression.  Old application IDs, dirty bits, and the
-- relative order of old watcher entries remain stable; mixed CSE outputs
-- preserve proposal order.
#guard
  match admittedDynamicTwice? with
  | some (before, state) =>
      state.programVersion == 2 && state.program.nodes.size == 8 &&
        state.applications.size == 7 && state.bindings.size == 3 &&
        applicationsPrefix before.applications state.applications &&
        state.queued.toList.take before.queued.size == before.queued.toList &&
        watcherSubsequences before.watchers state.watchers &&
        state.applications[5]?.any (fun application =>
          application.rule.index == 2 && application.node == node 7 &&
            application.generation == 2) &&
        state.applications[6]?.any (fun application =>
          application.rule.index == 0 && application.node == node 7 &&
            application.generation == 2) &&
        state.instanceHistory[1]?.any (fun event =>
          event.applications == [{ index := 3 }, { index := 5 }, { index := 5 }] &&
            event.newApplications == [{ index := 5 }] &&
            event.bindings.length == 3 && event.newBindings.length == 1)
  | none => false

def dynamicEqualityRequest : InstantiationRequest :=
  { dynamicRequest with
    equalities :=
      [{ left := .existing (node 0)
         right := .existing (node 1)
         payload := { index := 15 } }] }

def dynamicEqualityThenScope? : Option (Engine Rank × Engine Rank) := do
  let retained <- retainedDynamic?
  let origin <- retained.suggestions[0]?
  let first : RetainedSuggestion :=
    { origin with suggestion := .instantiate dynamicEqualityRequest }
  let before <- match retained.admitRetained first with
    | .admitted [fresh] state => if fresh == node 6 then some state else none
    | _ => none
  let secondRequest : InstantiationRequest :=
    { key := 53
      nodes := []
      equalities := []
      scopes := [existingDynamicScope]
      payload := { index := 16 } }
  let second : RetainedSuggestion :=
    { origin with suggestion := .instantiate secondRequest }
  match before.admitRetained second with
  | .admitted [] after => some (before, after)
  | _ => none

-- Applications and equalities use one dependency list.  A new application is
-- inserted before an older equality, so prefix stability would be false; the
-- required deterministic invariant is preservation of every old entry in its
-- old relative order.
#guard
  match dynamicEqualityThenScope? with
  | some (before, after) =>
      match before.watchers[0]?, after.watchers[0]? with
      | some old, some new =>
          old.length == 4 && new.length == 5 &&
            new.take old.length != old && listSubsequence old new &&
            watcherSubsequences before.watchers after.watchers
      | _, _ => false
  | none => false

/-- First create a generation-one node without a scope.  A later proposal
refers to an identical draft through `.proposed 0`; CSE resolves it to that old
node, so using it as a new scope input must raise the next event to generation
two. -/
def generationSeed? : Option (Engine Rank × RetainedSuggestion) := do
  let state <- match Engine.start rankDomain program #[scopedRule, dynamicRule]
      #[4, 6, 0, 0, 0, 9] limits #[scope] with
    | .ok state => some state
    | .error _ => none
  let (request, awaiting) <- match state.poll with
    | .request request awaiting => some (request, awaiting)
    | _ => none
  let seed : InstantiationRequest :=
    { key := 31
      nodes :=
        [{ domain := real
           op := { index := 1 }
           args := [.existing (node 2)] }]
      equalities := []
      payload := { index := 10 } }
  let retained <- match awaiting.submit
      (request.action.reply (.success [] [.instantiate seed] {})) with
    | .accepted _ state => some state
    | _ => none
  let origin <- retained.suggestions[0]?
  match retained.admitInstantiation { index := 0 } with
  | .admitted [fresh] state =>
      if fresh == node 6 then some (state, origin) else none
  | _ => none

def cseScopeRetained? : Option (Engine Rank × RetainedSuggestion) := do
  let (state, origin) <- generationSeed?
  let request : InstantiationRequest :=
    { key := 37
      nodes :=
        [{ domain := real
           op := { index := 1 }
           args := [.existing (node 2)] }]
      equalities := []
      scopes :=
        [{ rule := dynamicKey
           anchor := .proposed 0
           watches := [.proposed 0]
           writes := [] }]
      payload := { index := 11 } }
  some (state, { origin with suggestion := .instantiate request })

#guard
  match cseScopeRetained? with
  | some (state, retained) =>
      state.instantiationGeneration? retained == some 2 &&
        match state.admitRetained retained with
        | .admitted [] next =>
            next.program.nodes.size == 7 && next.metrics.generatedScopes == 1 &&
              next.instanceHistory[1]?.any (fun event => event.generation == 2)
        | _ => false
  | none => false

-- A scoped registration is dormant when no package matcher emitted a binding;
-- it is never silently reinterpreted as one local application per head node.
#guard
  match compileApplications program #[scopedRule] with
  | some applications => applications.isEmpty
  | none => false

def startError (rules : Array Registration) (bindings : Array ScopeBinding)
    (customLimits : Limits := limits) : Option StartError :=
  match Engine.start rankDomain program rules #[4, 6, 0, 0, 0, 9]
      customLimits bindings with
  | .ok _ => none
  | .error error => some error

#guard
  startError #[{ scopedRule with watches := [.result] }] #[scope] ==
    some .invalidRegistrations

#guard
  startError #[localRule] #[{ scope with rule := localKey }] == some .invalidBindings

#guard
  startError #[scopedRule] #[{ scope with anchor := node 2 }] == some .invalidBindings

#guard
  startError #[scopedRule] #[{ scope with watches := [node 0, node 0] }] ==
    some .invalidBindings

#guard
  startError #[scopedRule] #[{ scope with writes := [node 2, node 2] }] ==
    some .invalidBindings

#guard
  startError #[scopedRule] #[{ scope with watches := [node 99] }] ==
    some .invalidBindings

#guard startError #[scopedRule] #[scope, scope] == some .invalidBindings

-- Size limits are checked before malformed binding contents are traversed.
#guard
  startError #[scopedRule]
      #[{ scope with
          watches := [node 0, node 1, node 2, node 3, node 4, node 5, node 0] }]
      { limits with maxScopeNodes := 6 } == some (.resourceLimit .scopes)

#guard
  startError #[scopedRule] #[scope] { limits with maxApplications := 0 } ==
    some (.resourceLimit .applications)

#guard
  startError #[scopedRule] #[scope] { limits with maxQueueEntries := 0 } ==
    some (.resourceLimit .queueEntries)

end Hex.Interval.ScopeConformance
