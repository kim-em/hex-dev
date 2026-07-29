/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PackageRegistry

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
    handlers := #[{ registration := scopedRule, invoke := scopedInvoke }] }

def run? : Option (RunResult Rank (Registry Rank)) :=
  match Registry.buildWithin limits #[scopedPackage] with
  | .error _ => none
  | .ok registry =>
      if !registry.acceptsProgram program || !registry.acceptsLimits program limits then
        none
      else
        match Engine.start rankDomain program registry.registrations
            #[4, 6, 0, 0, 0, 9] limits #[scope] with
        | .error _ => none
        | .ok state => some (drive Registry.invoke 4 state registry)

#guard program.check
#guard extendedProgram.check

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
      { limits with maxNodes := 6 } == some (.resourceLimit .nodes)

#guard
  startError #[scopedRule] #[scope] { limits with maxApplications := 0 } ==
    some (.resourceLimit .applications)

#guard
  startError #[scopedRule] #[scope] { limits with maxQueueEntries := 0 } ==
    some (.resourceLimit .queueEntries)

end Hex.Interval.ScopeConformance
