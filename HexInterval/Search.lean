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
identifiers, keys, and payloads are explicitly non-preemptible. A callback
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

/-- A decoded session. Every mutating consumer rechecks this record; its public
constructor grants no authority. -/
structure Session (Fact Cause OfferId SemanticKey : Type) where
  branch : State.Branch Fact Cause
  rules : Array Registration
  bindings : Array ScopeBinding
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

def actionCurrent (limits : State.Limits) (branch : State.Branch Fact Cause)
    (rules : Array Registration) (bindings : Array ScopeBinding)
    (applicationGenerations equalityGenerations : Array Nat)
    (matcherEpoch serial : Nat)
    (action : Action) : Bool := Id.run do
  if action.serial != serial || action.programVersion != branch.programVersion ||
      limits.maxEffort < action.effort then
    return false
  let some applicationGeneration := applicationGenerations[action.application.index]?
    | return false
  if applicationGeneration != action.generation then return false
  let some registration := rules[action.rule.index]? | return false
  if registration.key != action.key || registration.kind != action.kind then return false
  let some instruction := branch.program.node? action.node | return false
  let some operation := branch.program.operation? instruction.op | return false
  if operation.key != registration.head || !allDistinct action.inputs ||
      !allDistinct action.writes || !allDistinct action.structuralInputs then return false
  for seen in action.inputs do
    let some version := branch.versions[seen.node.index]? | return false
    if version != seen.version then return false
  for node in action.writes do
    if (branch.program.node? node).isNone then return false
  for input in action.structuralInputs do
    match input.key with
    | .node node =>
        let some generation := branch.generations[node.index]? | return false
        if generation != input.generation then return false
    | .application application =>
        let some generation := applicationGenerations[application.index]? | return false
        if generation != input.generation then return false
    | .equality equality =>
        let some generation := equalityGenerations[equality.index]? | return false
        if generation != input.generation then return false
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
  return bindingValid && matcherValid

def Session.check [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    (envelope : Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey) : Bool := Id.run do
  if !session.branch.check ||
      !Registration.check session.branch.program session.rules ||
      !ScopeBinding.checkAll session.branch.program session.rules session.bindings ||
      envelope.state.maxRules < session.rules.size ||
      envelope.state.maxScopeNodes < session.bindings.size ||
      envelope.state.maxApplications < session.applicationGenerations.size ||
      envelope.state.maxEqualities < session.equalityGenerations.size ||
      !session.accounting.check envelope.search 0 ||
      !session.trace.check envelope.trace then return false
  let view := session.view
  match Policy.checkViewWithin envelope.policy measure session.branch.program view with
  | .error _ => return false
  | .ok _ => pure ()
  for offer in session.offers do
    if !actionCurrent envelope.state session.branch session.rules
        session.bindings session.applicationGenerations session.equalityGenerations
        session.matcherEpoch session.serial offer.action then
      return false
  return true

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

/-- Build one exact checked session transactionally. Offer generation remains
external; this builder only authenticates its complete returned snapshot. -/
def Session.startWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
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
  if !session.check envelope measure then throw .invalidSession
  pure session

/-- Install a newly generated complete offer snapshot only after validating it
against the exact current session. Failure preserves the preceding session. -/
def Session.refreshWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    (envelope : Envelope) (measure : Policy.Measure OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey)
    (offers : Array (Offer OfferId SemanticKey))
    (remaining : Policy.EngineBudgetView) (incomplete : Bool) :
    Except Error (Session Fact Cause OfferId SemanticKey) := do
  if !session.check envelope measure then throw .invalidSession
  let next := { session with offers, remaining, incomplete }
  if !next.check envelope measure then throw .invalidSession
  pure next

/-- Exact authenticated callback request. -/
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

/-- Revalidate the policy's complete echoed offer, then return the exact
controller-owned action request. -/
def prepareWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    [DecidableEq SemanticKey] (envelope : Envelope)
    (measure : Policy.Measure OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey)
    (decision : Policy.Decision OfferId SemanticKey) : Except Error (Request Fact OfferId SemanticKey) := do
  if !session.check envelope measure then throw .invalidSession
  let view := session.view
  let selected <-
    match Policy.checkDecisionWithin envelope.policy measure session.branch view decision with
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
      facts := session.branch.snapshot }

/-- Run a replaceable policy over the exact checked view. A selected or
dismissed offer is revalidated before its exact decision is returned; stopping
cannot mutate the session. Policy callback execution is non-preemptible. -/
def chooseWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    [DecidableEq SemanticKey] (envelope : Envelope)
    (measure : Policy.Measure OfferId SemanticKey)
    (policy : Policy.Interface Fact PolicyState OfferId SemanticKey)
    (policyState : PolicyState) (session : Session Fact Cause OfferId SemanticKey) :
    Except Error (Choice PolicyState OfferId SemanticKey) := do
  if !session.check envelope measure then throw .invalidSession
  let view := session.view
  match policy.choose policyState view with
  | .stop next => pure (.stopped (.policyStop view.offers.size) next)
  | .select offer next =>
      let decision := Policy.select view offer
      let _ <- prepareWithin envelope measure session decision
      pure (.select decision next)
  | .dismiss offer next =>
      let decision := Policy.select view offer
      let _ <- prepareWithin envelope measure session decision
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

/-- Validate and commit the whole returned delta transactionally. Every event
must be an exact successor for a node in the selected action's write set. The
returned contradiction bit is runtime status only. -/
def acceptWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    [DecidableEq SemanticKey] (envelope : Envelope)
    (measure : Policy.Measure OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey)
    (decision : Policy.Decision OfferId SemanticKey)
    (reply : Reply Fact Cause OfferId SemanticKey) : Except Error (Step Fact Cause OfferId SemanticKey) := do
  if session.accounting.steps >= envelope.search.maxSteps then
    return .stopped (.resource .steps) session
  let request <- prepareWithin envelope measure session decision
  match reply with
  | .failure code diagnostic =>
      if envelope.trace.maxCode < code then throw .malformedOutcome
      let trace <- appendDiagnostic envelope.trace session.trace diagnostic
      return .stopped (.callbackFailure code) { session with trace }
  | .outcome outcome =>
      if !sameReply request outcome then throw .staleReply
      if envelope.state.maxOutcomeCandidates < outcome.updates.size then
        throw .outcomeLimit
      let mut branch := session.branch
      for event in outcome.updates do
        if !request.action.writes.contains event.node then
          throw (.unauthorizedWrite event.node)
        let next <-
          match branch.pushWithin envelope.state event outcome.contradiction with
          | .ok updated => pure updated
          | .error error => throw (.state error)
        branch := next
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

/-- Invoke an arbitrary callback and then pass its decoded result through
`acceptWithin`. Callback execution itself is deliberately non-preemptible and
has no mutation authority. -/
def invokeWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    [DecidableEq SemanticKey] (envelope : Envelope)
    (measure : Policy.Measure OfferId SemanticKey)
    (callback : Request Fact OfferId SemanticKey -> Reply Fact Cause OfferId SemanticKey)
    (session : Session Fact Cause OfferId SemanticKey)
    (decision : Policy.Decision OfferId SemanticKey) : Except Error (Step Fact Cause OfferId SemanticKey) := do
  let request <- prepareWithin envelope measure session decision
  acceptWithin envelope measure session decision (callback request)

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

def Leaf.asParent (leaf : Leaf Fact Cause Payload) : Parent Fact Cause :=
  { scope := leaf.scope, depth := leaf.depth, branch := leaf.branch }

/-- Restore the exact retained parent, including versions, provenance, scope,
and contradiction state. -/
def Leaf.restoreParent? (leaf : Leaf Fact Cause Payload) : Option (Parent Fact Cause) :=
  leaf.parent

/-- Build a root frontier after all count caps admit it. -/
def startFrontierWithin (limits : Limits) (root : Leaf Fact Cause Payload) :
    Except Error (Accounting × Frontier (Leaf Fact Cause Payload)) := do
  if limits.maxLeaves < 1 then throw (.resource .leaves)
  if limits.maxScopes < 1 then throw (.resource .scopes)
  if limits.maxFrontier < 1 then throw (.resource .frontier)
  if root.depth != 0 || root.parent.isSome || !root.branch.check then throw .invalidSession
  pure ({ nextScope := root.scope.index + 1 }, .singleton root)

/-- Pop the stable next pending leaf. -/
def pop (frontier : Frontier α) : Option (α × Frontier α) := do
  let head <- frontier.head?
  pure (head, frontier.tail)

/-- Retain a terminal leaf and charge exactly one processing step. -/
def settleWithin (limits : Limits) (frontierCount : Nat) (accounting : Accounting) :
    Except Error Accounting := do
  if !accounting.check limits (frontierCount + 1) then throw .invalidSession
  if accounting.steps >= limits.maxSteps then throw (.resource .steps)
  pure { accounting with steps := accounting.steps + 1 }

/-- Admit an exact binary split and schedule its children transactionally.
The package owns child semantics; generic search authenticates the retained
parent, checked child branches, fresh scopes, depth, and global resources. -/
def splitWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (order : Order) (accounting : Accounting)
    (parent : Leaf Fact Cause Payload) (rest : Frontier (Leaf Fact Cause Payload))
    (left right : Leaf Fact Cause Payload) :
    Except Error (Accounting × Frontier (Leaf Fact Cause Payload)) := do
  if !accounting.check limits (rest.pending.length + 1) then throw .invalidSession
  if accounting.steps >= limits.maxSteps then throw (.resource .steps)
  if accounting.splits >= limits.maxSplits then throw (.resource .splits)
  if accounting.leaves >= limits.maxLeaves then throw (.resource .leaves)
  if accounting.scopes + 2 > limits.maxScopes then throw (.resource .scopes)
  let depth := parent.depth + 1
  if limits.maxDepth < depth then throw (.resource .depth)
  let expected := parent.asParent
  if left.depth != depth || right.depth != depth || left.parent != some expected ||
      right.parent != some expected || left.scope == right.scope ||
      left.scope == parent.scope || right.scope == parent.scope ||
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
