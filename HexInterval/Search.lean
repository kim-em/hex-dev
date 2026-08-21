/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Policy

@[expose] public section

/-!
# Authenticated search sessions

This module is the supported, Mathlib-free ownership boundary for generic
search. It authenticates policy choices against immutable views, binds the
selected offer to an exact `Action`, and transactionally validates untrusted
callback updates against `State.Branch`. It also supplies bounded tree
accounting and stable depth-first/breadth-first frontier operations.

The callback invocation and equality on caller-selected facts, causes,
identifiers, and keys are explicitly non-preemptible. A callback
must bound construction before returning. Search checks the returned action,
counts, versions, write authority, retained diagnostic bytes, and declared
work before it commits any branch mutation. Neither an accepted callback
result nor a runtime contradiction is theorem evidence.

Concrete callbacks, offer generation, package assembly, policy algorithms,
storage choices, split semantics, and proof replay remain outside this module.
-/

namespace Hex.Interval.Search

/-- Stable pending-leaf order. Equal-priority entries retain insertion order. -/
inductive Order where
  | depthFirst
  | breadthFirst
  deriving DecidableEq, Repr

/-- Global run and retained-tree limits. `leafFuel` bounds one package-owned
leaf driver; this layer only retains the value and does not interpret a
callback step. -/
structure Limits where
  maxSteps : Nat
  maxSplits : Nat
  maxLeaves : Nat
  maxFrontier : Nat
  maxDepth : Nat
  maxScopes : Nat
  leafFuel : Nat
  deriving DecidableEq, Repr

/-- Exact global accounting. `leaves` counts retained current leaves, including
settled leaves; a binary split increments it by one. -/
structure Accounting where
  steps : Nat := 0
  splits : Nat := 0
  leaves : Nat := 1
  scopes : Nat := 1
  nextScope : Nat := 1
  deriving DecidableEq, Repr

def Accounting.check (limits : Limits) (frontierCount : Nat)
    (accounting : Accounting) : Bool :=
    accounting.leaves == accounting.splits + 1 &&
    accounting.scopes == accounting.splits * 2 + 1 &&
    accounting.scopes ≤ accounting.nextScope &&
    accounting.splits ≤ accounting.steps && frontierCount ≤ accounting.leaves &&
    accounting.steps ≤ limits.maxSteps && accounting.splits ≤ limits.maxSplits &&
    accounting.leaves ≤ limits.maxLeaves && accounting.scopes ≤ limits.maxScopes &&
    frontierCount ≤ limits.maxFrontier

inductive Resource where
  | steps
  | splits
  | leaves
  | frontier
  | depth
  | scopes
  | state (resource : State.Resource)
  deriving DecidableEq, Repr

/-- Precise generic stop classes. Package-specific errors remain an opaque
callback code and cannot become proof evidence. -/
inductive Stop (Reached Split : Type) where
  | target (reached : Reached)
  | saturated
  | contradiction
  | split (plan : Split)
  | policyStop (liveOffers : Nat)
  | incomplete
  | callbackFailure (code : Nat)
  | resource (resource : Resource)
  | malformed

/-- A stable front-to-back pending sequence. -/
structure Frontier (α : Type) where
  pending : List α
  deriving DecidableEq, Repr

namespace Frontier

def singleton (item : α) : Frontier α := { pending := [item] }

def isEmpty (frontier : Frontier α) : Bool := frontier.pending.isEmpty

def head? (frontier : Frontier α) : Option α := frontier.pending.head?

def tail (frontier : Frontier α) : Frontier α := { pending := frontier.pending.tail }

/-- Schedule left-to-right fresh children either before or after the stable
old suffix. -/
def schedule (order : Order) (rest : Frontier α) (fresh : List α) : Frontier α :=
  { pending := match order with
    | .depthFirst => fresh ++ rest.pending
    | .breadthFirst => rest.pending ++ fresh }

end Frontier

/-- One controller-owned offer and the exact action it authorizes. The policy
sees only `view`. -/
structure Offer (OfferId SemanticKey : Type) where
  view : Policy.OfferView OfferId SemanticKey
  action : Action
  deriving DecidableEq

/-- All supported envelopes for one authenticated session. -/
structure Envelope where
  state : State.Limits
  policy : Policy.Limits
  trace : Trace.Limit
  search : Limits
  deriving DecidableEq, Repr

inductive Error where
  | invalidSession
  | policy (error : Policy.Error)
  | staleReply
  | malformedOutcome
  | unauthorizedWrite (node : NodeId)
  | outcomeLimit
  | state (error : State.BranchError)
  | trace
  | resource (resource : Resource)
  deriving DecidableEq, Repr

/-- A decoded session. Every mutating consumer rechecks this record; its public
constructor grants no authority. -/
structure Session (Fact Cause OfferId SemanticKey : Type) where
  branch : State.Branch Fact Cause
  rules : Array Registration
  bindings : Array ScopeBinding
  /-- Generation stamps for opaque scheduler application handles. This layer
  does not retain an application table and therefore does not infer a
  rule/anchor pair from the compact identifier. -/
  applicationGenerations : Array Nat
  equalityGenerations : Array Nat
  matcherEpoch : Nat
  scope : Policy.ScopeId
  serial : Nat
  offers : Array (Offer OfferId SemanticKey)
  remaining : Policy.EngineBudgetView
  incomplete : Bool
  trace : Trace.Log
  accounting : Accounting

def Session.view (session : Session Fact Cause OfferId SemanticKey) :
    Policy.View Fact OfferId SemanticKey :=
  { scope := session.scope
    serial := session.serial
    programVersion := session.branch.programVersion
    offers := session.offers.map (·.view)
    facts := session.branch.snapshot
    remaining := session.remaining
    incomplete := session.incomplete }

/-- Check a decoded list against a cap without traversing beyond the first
disallowed cell. -/
def listWithin : Nat -> List α -> Bool
  | _, [] => true
  | 0, _ :: _ => false
  | limit + 1, _ :: rest => listWithin limit rest

private def stateResource (resource : State.Resource) : Error :=
  .resource (.state resource)

private def preflightProgram (limits : State.Limits) (program : Program) : Except Error Unit := do
  if limits.maxOperations < program.operations.size then
    throw (stateResource .operations)
  if limits.maxNodes < program.nodes.size then throw (stateResource .nodes)
  if program.operations.any (fun operation => !listWithin limits.maxArity operation.inputs) ||
      program.nodes.any (fun node => !listWithin limits.maxArity node.args) then
    throw (stateResource .arity)

private def preflightBranch (limits : State.Limits)
    (branch : State.Branch Fact Cause) : Except Error Unit := do
  preflightProgram limits branch.baseProgram
  preflightProgram limits branch.program
  if limits.maxAcceptedFacts < branch.history.size then
    throw (stateResource .acceptedFacts)
  if limits.maxNodes < branch.initialFacts.size ||
      limits.maxNodes < branch.seeds.size ||
      limits.maxNodes < branch.versions.size ||
      limits.maxNodes < branch.generations.size ||
      limits.maxNodes < branch.depths.size then
    throw (stateResource .nodes)
  if branch.initialFacts.size != branch.baseProgram.nodes.size ||
      branch.program.nodes.size < branch.baseProgram.nodes.size ||
      branch.seeds.size != branch.program.nodes.size - branch.baseProgram.nodes.size ||
      branch.versions.size != branch.program.nodes.size ||
      branch.generations.size != branch.program.nodes.size ||
      branch.depths.size != branch.program.nodes.size then
    throw .invalidSession
  if branch.depths.any (fun depth => limits.maxNodeDepth < depth) then
    throw (stateResource .nodeDepth)
  if branch.generations.any (fun generation => limits.maxGeneration < generation) then
    throw (stateResource .generation)

private def preflightAction (limits : State.Limits) (rules : Array Registration)
    (action : Action) : Except Error Unit := do
  if limits.maxEffort < action.effort then throw (stateResource .effort)
  let some registration := rules[action.rule.index]? | throw .invalidSession
  let portLimit := match registration.binding with
    | .local => limits.maxArity + 1
    | .scoped => limits.maxScopeNodes
    | .global => 0
  let portResource := match registration.binding with
    | .local => State.Resource.arity
    | .scoped => State.Resource.scopes
    | .global => State.Resource.arity
  if !listWithin portLimit action.inputs || !listWithin portLimit action.writes then
    throw (stateResource portResource)
  if !listWithin limits.matcherBatchSize action.structuralInputs then
    throw (stateResource .matcherVisits)

private def preflightSession (limits : State.Limits)
    (session : Session Fact Cause OfferId SemanticKey) : Except Error Unit := do
  preflightBranch limits session.branch
  if limits.maxRules < session.rules.size then throw (stateResource .rules)
  if limits.maxApplications < session.bindings.size ||
      limits.maxApplications < session.applicationGenerations.size then
    throw (stateResource .applications)
  if limits.maxEqualities < session.equalityGenerations.size then
    throw (stateResource .equalities)
  if session.rules.any (fun rule => limits.maxEffort < rule.initialEffort) then
    throw (stateResource .effort)
  if session.rules.any (fun rule =>
      !listWithin (limits.maxArity + 1) rule.watches ||
        !listWithin (limits.maxArity + 1) rule.writes) then
    throw (stateResource .arity)
  if session.bindings.any (fun binding =>
      !listWithin limits.maxScopeNodes binding.watches ||
        !listWithin limits.maxScopeNodes binding.writes) then
    throw (stateResource .scopes)
  if limits.matcherBatchSize == 0 &&
      session.rules.any (fun rule => rule.matchWatch == .network) then
    throw (stateResource .matcherVisits)
  if session.applicationGenerations.any (fun generation => limits.maxGeneration < generation) ||
      session.equalityGenerations.any (fun generation => limits.maxGeneration < generation) then
    throw (stateResource .generation)
  for offer in session.offers do
    preflightAction limits session.rules offer.action

private def actionCurrentWithin (limits : State.Limits) (branch : State.Branch Fact Cause)
    (rules : Array Registration) (bindings : Array ScopeBinding)
    (applicationGenerations equalityGenerations : Array Nat)
    (matcherEpoch serial : Nat)
    (action : Action) : Except Error Unit := do
  if action.serial != serial || action.programVersion != branch.programVersion ||
      limits.maxEffort < action.effort then
    if limits.maxEffort < action.effort then throw (stateResource .effort)
    else throw .invalidSession
  let some applicationGeneration := applicationGenerations[action.application.index]?
    | throw .invalidSession
  if applicationGeneration != action.generation then throw .invalidSession
  let some registration := rules[action.rule.index]? | throw .invalidSession
  if registration.key != action.key || registration.kind != action.kind then
    throw .invalidSession
  preflightAction limits rules action
  let some instruction := branch.program.node? action.node | throw .invalidSession
  let some operation := branch.program.operation? instruction.op | throw .invalidSession
  if operation.key != registration.head || !allDistinct action.inputs ||
      !allDistinct action.writes || !allDistinct action.structuralInputs then
    throw .invalidSession
  for seen in action.inputs do
    let some version := branch.versions[seen.node.index]? | throw .invalidSession
    if version != seen.version then throw .invalidSession
  for node in action.writes do
    if (branch.program.node? node).isNone then throw .invalidSession
  for input in action.structuralInputs do
    match input.key with
    | .node node =>
        let some generation := branch.generations[node.index]? | throw .invalidSession
        if generation != input.generation then throw .invalidSession
    | .application application =>
        let some generation := applicationGenerations[application.index]? | throw .invalidSession
        if generation != input.generation then throw .invalidSession
    | .equality equality =>
        let some generation := equalityGenerations[equality.index]? | throw .invalidSession
        if generation != input.generation then throw .invalidSession
  let inputNodes := action.inputs.map (·.node)
  let bindingValid := match registration.binding with
    | .local =>
        Slot.resolveAll? action.node instruction registration.watches == some inputNodes &&
          Slot.resolveAll? action.node instruction registration.writes == some action.writes
    | .scoped =>
        bindings.any fun binding =>
          binding.rule == action.key && binding.anchor == action.node &&
            binding.watches == inputNodes && binding.writes == action.writes
    | .global => inputNodes.isEmpty && action.writes.isEmpty
  let matcherValid := match registration.matchWatch with
    | .none => action.matcherEpoch.isNone && action.structuralInputs.isEmpty
    | .network => action.matcherEpoch == some matcherEpoch && !action.structuralInputs.isEmpty
  if !bindingValid || !matcherValid then throw .invalidSession

opaque actionCurrent (limits : State.Limits) (branch : State.Branch Fact Cause)
    (rules : Array Registration) (bindings : Array ScopeBinding)
    (applicationGenerations equalityGenerations : Array Nat)
    (matcherEpoch serial : Nat) (action : Action) : Bool :=
  (actionCurrentWithin limits branch rules bindings applicationGenerations
    equalityGenerations matcherEpoch serial action).isOk

private structure Checked (Fact OfferId SemanticKey : Type) where
  view : Policy.View Fact OfferId SemanticKey

private def authenticate [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    (envelope : Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey) :
    Except Error (Checked Fact OfferId SemanticKey) := do
  if envelope.policy.maxOffers < session.offers.size then
    throw (.policy .offerLimit)
  preflightSession envelope.state session
  let some snapshot := session.branch.checkedSnapshot? | throw .invalidSession
  if !Registration.check session.branch.program session.rules ||
      !ScopeBinding.checkAll session.branch.program session.rules session.bindings ||
      !session.accounting.check envelope.search 0 ||
      !session.trace.check envelope.trace then
    throw .invalidSession
  let view : Policy.View Fact OfferId SemanticKey :=
    { scope := session.scope
      serial := session.serial
      programVersion := session.branch.programVersion
      offers := session.offers.map (·.view)
      facts := snapshot
      remaining := session.remaining
      incomplete := session.incomplete }
  match Policy.checkOffersWithin envelope.policy measure view with
  | .error error => throw (.policy error)
  | .ok _ => pure ()
  for offer in session.offers do
    actionCurrentWithin envelope.state session.branch session.rules
      session.bindings session.applicationGenerations session.equalityGenerations
      session.matcherEpoch session.serial offer.action
  pure { view }

opaque Session.check [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    (envelope : Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey) : Bool :=
  (authenticate envelope measure session).isOk

/-- Build one exact checked session transactionally. Offer generation remains
external; this builder only authenticates its complete returned snapshot. -/
opaque Session.startWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    (envelope : Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (branch : State.Branch Fact Cause) (rules : Array Registration)
    (bindings : Array ScopeBinding) (applicationGenerations equalityGenerations : Array Nat)
    (matcherEpoch : Nat) (scope : Policy.ScopeId)
    (offers : Array (Offer OfferId SemanticKey))
    (remaining : Policy.EngineBudgetView := {}) (incomplete : Bool := false) :
    Except Error (Session Fact Cause OfferId SemanticKey) := do
  let session : Session Fact Cause OfferId SemanticKey :=
    { branch
      rules
      bindings
      applicationGenerations
      equalityGenerations
      matcherEpoch
      scope
      serial := 0
      offers
      remaining
      incomplete
      trace := {}
      accounting := { nextScope := scope.index + 1 } }
  let _ <- authenticate envelope measure session
  pure session

/-- Install a newly generated complete offer snapshot only after validating it
against the exact current session. Failure preserves the preceding session. -/
opaque Session.refreshWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    (envelope : Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey)
    (offers : Array (Offer OfferId SemanticKey))
    (remaining : Policy.EngineBudgetView) (incomplete : Bool) :
    Except Error (Session Fact Cause OfferId SemanticKey) := do
  let next := { session with offers, remaining, incomplete }
  let _ <- authenticate envelope measure next
  pure next

/-- Exact authenticated callback request. Rule, anchor, kind, ports, versions,
and generations have been checked independently. `action.application` remains
an opaque generation-stamped scheduler handle at this layer, not authority for
the rule or anchor. -/
structure Request (Fact OfferId SemanticKey : Type) where
  scope : Policy.ScopeId
  serial : Nat
  programVersion : Nat
  offer : Policy.OfferView OfferId SemanticKey
  action : Action
  facts : Snapshot Fact

/-- Untrusted callback delta. All identity fields must echo the exact request. -/
structure Outcome (Fact Cause OfferId SemanticKey : Type) where
  scope : Policy.ScopeId
  serial : Nat
  programVersion : Nat
  offer : Policy.OfferView OfferId SemanticKey
  action : Action
  updates : Array (State.Update Fact Cause)
  contradiction : Bool := false
  diagnostic : Option Trace.Event := none

/-- A callback either returns an untrusted delta or an exact bounded failure
code. Both forms may carry a diagnostic assembled outside the preemptible
envelope. -/
inductive Reply (Fact Cause OfferId SemanticKey : Type)
  | outcome (outcome : Outcome Fact Cause OfferId SemanticKey)
  | failure (code : Nat) (diagnostic : Option Trace.Event := none)

/-- A checked callback step either commits a replacement session or stops with
an unchanged proof state. -/
inductive Step (Fact Cause OfferId SemanticKey : Type)
  | applied (session : Session Fact Cause OfferId SemanticKey)
  | stopped (stop : Stop Unit Unit) (session : Session Fact Cause OfferId SemanticKey)

/-- Checked interpretation of an external policy result. -/
inductive Choice (PolicyState OfferId SemanticKey : Type)
  | select (decision : Policy.Decision OfferId SemanticKey) (next : PolicyState)
  | dismiss (decision : Policy.Decision OfferId SemanticKey) (next : PolicyState)
  | stopped (stop : Stop Unit Unit) (next : PolicyState)

variable {Fact Cause OfferId SemanticKey : Type}

private def prepareChecked [DecidableEq OfferId] [DecidableEq SemanticKey]
    (session : Session Fact Cause OfferId SemanticKey)
    (checked : Checked Fact OfferId SemanticKey)
    (decision : Policy.Decision OfferId SemanticKey) :
    Except Error (Request Fact OfferId SemanticKey) := do
  let selected <-
    match Policy.revalidate checked.view decision with
    | .ok selected => pure selected
    | .error error => throw (.policy error)
  let some offer := session.offers.find? fun offer => offer.view == selected
    | throw .invalidSession
  pure
    { scope := session.scope
      serial := session.serial
      programVersion := session.branch.programVersion
      offer := offer.view
      action := offer.action
      facts := checked.view.facts }

/-- Revalidate the policy's complete echoed offer, then return the exact
controller-owned action request. -/
opaque prepareWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    [DecidableEq SemanticKey] (envelope : Envelope)
    (measure : Policy.Measure OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey)
    (decision : Policy.Decision OfferId SemanticKey) : Except Error (Request Fact OfferId SemanticKey) := do
  let checked <- authenticate envelope measure session
  prepareChecked session checked decision

/-- Run a replaceable policy over the exact checked view. A selected or
dismissed offer is revalidated before its exact decision is returned; stopping
cannot mutate the session. Policy callback execution is non-preemptible. -/
opaque chooseWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    [DecidableEq SemanticKey] (envelope : Envelope)
    (measure : Policy.Measure OfferId SemanticKey)
    (policy : Policy.Interface Fact PolicyState OfferId SemanticKey)
    (policyState : PolicyState) (session : Session Fact Cause OfferId SemanticKey) :
    Except Error (Choice PolicyState OfferId SemanticKey) := do
  let checked <- authenticate envelope measure session
  match policy.choose policyState checked.view with
  | .stop next => pure (.stopped (.policyStop checked.view.offers.size) next)
  | .select offer next =>
      let decision := Policy.select checked.view offer
      let _ <- prepareChecked session checked decision
      pure (.select decision next)
  | .dismiss offer next =>
      let decision := Policy.select checked.view offer
      let _ <- prepareChecked session checked decision
      pure (.dismiss decision next)

def appendDiagnostic (limit : Trace.Limit) (log : Trace.Log)
    (diagnostic : Option Trace.Event) : Except Error Trace.Log :=
  match diagnostic with
  | none => pure log
  | some event =>
      match log.append limit event with
      | .retained next | .truncated next => pure next
      | .malformed => throw .trace

def sameReply [DecidableEq OfferId] [DecidableEq SemanticKey]
    (request : Request Fact OfferId SemanticKey)
    (outcome : Outcome Fact Cause OfferId SemanticKey) : Bool :=
  outcome.scope == request.scope && outcome.serial == request.serial &&
    outcome.programVersion == request.programVersion && outcome.offer == request.offer &&
    outcome.action == request.action

private def pushChecked (branch : State.Branch Fact Cause)
    (event : State.Update Fact Cause) (contradiction : Bool) :
    Except Error (State.Branch Fact Cause) := do
  if event.programVersion != branch.programVersion then
    throw (.state .wrongProgramVersion)
  let some current := branch.versions[event.node.index]?
    | throw (.state (.staleVersion event.node))
  if event.previous.node != event.node || event.previous.version != current ||
      event.version != current + 1 then
    throw (.state (.staleVersion event.node))
  pure
    { branch with
      versions := branch.versions.set! event.node.index event.version
      history := branch.history.push event
      contradictory := branch.contradictory || contradiction }

private def acceptChecked [DecidableEq OfferId] [DecidableEq SemanticKey]
    (envelope : Envelope) (session : Session Fact Cause OfferId SemanticKey)
    (request : Request Fact OfferId SemanticKey)
    (reply : Reply Fact Cause OfferId SemanticKey) :
    Except Error (Step Fact Cause OfferId SemanticKey) := do
  match reply with
  | .failure code diagnostic =>
      if envelope.trace.maxCode < code then throw .malformedOutcome
      let trace <- appendDiagnostic envelope.trace session.trace diagnostic
      return .stopped (.callbackFailure code) { session with trace }
  | .outcome outcome =>
      if !sameReply request outcome then throw .staleReply
      if envelope.state.maxOutcomeCandidates < outcome.updates.size then
        throw .outcomeLimit
      if envelope.state.maxAcceptedFacts < outcome.updates.size ||
          envelope.state.maxAcceptedFacts - outcome.updates.size < session.branch.history.size then
        throw (stateResource .acceptedFacts)
      let mut branch := session.branch
      for event in outcome.updates do
        if !request.action.writes.contains event.node then
          throw (.unauthorizedWrite event.node)
        branch <- pushChecked branch event outcome.contradiction
      if outcome.contradiction && outcome.updates.isEmpty then throw .malformedOutcome
      let trace <- appendDiagnostic envelope.trace session.trace outcome.diagnostic
      let next : Session Fact Cause OfferId SemanticKey :=
        { session with
          branch
          serial := session.serial + 1
          offers := #[]
          incomplete := true
          trace
          accounting := { session.accounting with steps := session.accounting.steps + 1 } }
      pure (.applied next)

/-- Validate and commit the whole returned delta transactionally. Every event
must be an exact successor for a node in the selected action's write set. The
returned contradiction bit is runtime status only. -/
opaque acceptWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    [DecidableEq SemanticKey] (envelope : Envelope)
    (measure : Policy.Measure OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey)
    (decision : Policy.Decision OfferId SemanticKey)
    (reply : Reply Fact Cause OfferId SemanticKey) : Except Error (Step Fact Cause OfferId SemanticKey) := do
  let checked <- authenticate envelope measure session
  let request <- prepareChecked session checked decision
  if session.accounting.steps >= envelope.search.maxSteps then
    return .stopped (.resource .steps) session
  acceptChecked envelope session request reply

/-- Invoke an arbitrary callback and then pass its decoded result through
`acceptWithin`. Callback execution itself is deliberately non-preemptible and
has no mutation authority. -/
opaque invokeWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    [DecidableEq SemanticKey] (envelope : Envelope)
    (measure : Policy.Measure OfferId SemanticKey)
    (callback : Request Fact OfferId SemanticKey -> Reply Fact Cause OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey)
    (decision : Policy.Decision OfferId SemanticKey) : Except Error (Step Fact Cause OfferId SemanticKey) := do
  let checked <- authenticate envelope measure session
  let request <- prepareChecked session checked decision
  if session.accounting.steps >= envelope.search.maxSteps then
    return .stopped (.resource .steps) session
  acceptChecked envelope session request (callback request)

/-- Exact retained parent snapshot for a child. -/
structure Parent (Fact Cause : Type) where
  scope : Policy.ScopeId
  depth : Nat
  branch : State.Branch Fact Cause
  deriving DecidableEq

/-- One pending leaf. Payload construction is outside the preemptible search
envelope. -/
structure Leaf (Fact Cause Payload : Type) where
  scope : Policy.ScopeId
  depth : Nat
  branch : State.Branch Fact Cause
  parent : Option (Parent Fact Cause) := none
  payload : Payload
  deriving DecidableEq

def Leaf.asParent (leaf : Leaf Fact Cause Payload) : Parent Fact Cause :=
  { scope := leaf.scope, depth := leaf.depth, branch := leaf.branch }

/-- Restore the exact retained parent, including versions, provenance, scope,
and contradiction state. -/
def Leaf.restoreParent? (leaf : Leaf Fact Cause Payload) : Option (Parent Fact Cause) :=
  leaf.parent

/-- Build a root frontier after all structural and count caps admit it. -/
opaque startFrontierWithin (stateLimits : State.Limits) (limits : Limits)
    (root : Leaf Fact Cause Payload) :
    Except Error (Accounting × Frontier (Leaf Fact Cause Payload)) := do
  if limits.maxLeaves < 1 then throw (.resource .leaves)
  if limits.maxScopes < 1 then throw (.resource .scopes)
  if limits.maxFrontier < 1 then throw (.resource .frontier)
  preflightBranch stateLimits root.branch
  if root.depth != 0 || root.parent.isSome || !root.branch.check then throw .invalidSession
  pure ({ nextScope := root.scope.index + 1 }, .singleton root)

/-- Pop the stable next pending leaf. -/
def pop (frontier : Frontier α) : Option (α × Frontier α) := do
  let head <- frontier.head?
  pure (head, frontier.tail)

/-- Retain the authenticated frontier head as a terminal leaf and charge
exactly one processing step. The caller cannot substitute a detached count. -/
def settleWithin (limits : Limits) (frontier : Frontier α) (accounting : Accounting) :
    Except Error Accounting := do
  if !listWithin limits.maxFrontier frontier.pending then throw (.resource .frontier)
  if frontier.pending.isEmpty ||
      !accounting.check limits frontier.pending.length then throw .invalidSession
  if accounting.steps >= limits.maxSteps then throw (.resource .steps)
  pure { accounting with steps := accounting.steps + 1 }

/-- Admit an exact binary split and schedule its children transactionally.
The package owns child semantics; generic search authenticates the retained
frontier head as the parent, checked child branches, fresh scopes, depth, and
global resources. -/
opaque splitWithin [DecidableEq Fact] [DecidableEq Cause]
    (stateLimits : State.Limits) (limits : Limits) (order : Order)
    (accounting : Accounting) (frontier : Frontier (Leaf Fact Cause Payload))
    (left right : Leaf Fact Cause Payload) :
    Except Error (Accounting × Frontier (Leaf Fact Cause Payload)) := do
  if !listWithin limits.maxFrontier frontier.pending then throw (.resource .frontier)
  for pending in frontier.pending do
    preflightBranch stateLimits pending.branch
    match pending.parent with
    | none => pure ()
    | some retained => preflightBranch stateLimits retained.branch
  if !allDistinct (frontier.pending.map (·.scope)) then throw .invalidSession
  if !accounting.check limits frontier.pending.length then throw .invalidSession
  let some (parent, rest) := pop frontier | throw .invalidSession
  if accounting.steps >= limits.maxSteps then throw (.resource .steps)
  if accounting.splits >= limits.maxSplits then throw (.resource .splits)
  if accounting.leaves >= limits.maxLeaves then throw (.resource .leaves)
  if accounting.scopes + 2 > limits.maxScopes then throw (.resource .scopes)
  let depth := parent.depth + 1
  if limits.maxDepth < depth then throw (.resource .depth)
  preflightBranch stateLimits left.branch
  preflightBranch stateLimits right.branch
  let expected := parent.asParent
  let some leftParent := left.parent | throw .invalidSession
  let some rightParent := right.parent | throw .invalidSession
  preflightBranch stateLimits leftParent.branch
  preflightBranch stateLimits rightParent.branch
  if !parent.branch.check || left.depth != depth || right.depth != depth ||
      leftParent != expected || rightParent != expected ||
      left.scope == right.scope || left.scope == parent.scope || right.scope == parent.scope ||
      rest.pending.any (fun pending => pending.scope == left.scope || pending.scope == right.scope) ||
      left.scope.index != accounting.nextScope ||
      right.scope.index != accounting.nextScope + 1 ||
      !left.branch.check || !right.branch.check then throw .invalidSession
  if limits.maxFrontier < rest.pending.length + 2 then throw (.resource .frontier)
  let accounting :=
    { steps := accounting.steps + 1
      splits := accounting.splits + 1
      leaves := accounting.leaves + 1
      scopes := accounting.scopes + 2
      nextScope := accounting.nextScope + 2 }
  pure (accounting, rest.schedule order [left, right])

end Hex.Interval.Search
