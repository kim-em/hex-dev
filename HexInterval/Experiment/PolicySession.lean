/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PackageRegistry
public import HexInterval.Experiment.Policy

@[expose] public section

/-!
# Proof-producing policy sessions

This experiment is the ownership boundary shared by arbitrary function
packages and an external search policy.  One private-constructor session owns
the policy state, the exact heterogeneous package registry which compiled its
engine, the immutable proof-payload arena, every configured resource envelope,
and the monotone liveness and completeness state.

The policy can only echo a checked offer through `Session.choose`. A selected
rule or retry is routed through `Registry.invokePlanned`; the resulting plan
and exact handler replay snapshot stay paired through bounded format checking,
prospective freezing, and relocation through the snapshot's sealed `freeze`
operation. The new arena is committed only after `Policy.State.submit` accepts
the relocated reply. Malformed evidence and package-local use, atom, or schema
excess, including draft-count and draft-cell excess, consume a failed reply and
preserve a live incomplete session; remaining whole-run entry or body-cell
exhaustion after earlier commits is fatal. Instantiation, equality contraction,
dismissal, and split preparation stay inside the same session boundary. No
public operation accepts a separately assembled engine, registry, or arena.
-/

namespace Hex.Interval.Experiment.PolicySession

open Propagator

local notation "PolicyDecision" =>
  Hex.Interval.Policy.Decision Propagator.Policy.OfferId Propagator.Policy.OfferKey
local notation "PolicyView" =>
  Hex.Interval.Policy.View

/-- All deterministic envelopes used to assemble one policy session. -/
structure Limits where
  engine : Hex.Interval.State.Limits
  policy : Propagator.Policy.Limits
  arena : PayloadArena.Limits
  deriving DecidableEq, Repr

/-- Failure while assembling one coherent policy-controlled run. -/
inductive StartError where
  | registry (error : RegistryError)
  | programRejected
  | incoherentLimits
  | limitsRejected
  | engine (error : Propagator.StartError)
  deriving DecidableEq, Repr

/-- A proof-producing policy state. `state` privately owns the engine together
with its policy frontier. Public projections support inspection, while the
private constructor prevents a caller from replacing that engine, the exact
registry, or the arena with a component from another run. -/
structure Session (Fact : Type) where
  private mk ::
  state : Propagator.Policy.State Fact
  registry : Registry Fact
  arena : PayloadArena.Arena
  limits : Limits
  /-- Required work was lost outside the policy state's own accounting. -/
  droppedWork : Bool
  live : Bool

private def make (state : Propagator.Policy.State Fact)
    (registry : Registry Fact) (limits : Limits) : Session Fact :=
  { state
    registry
    arena := .empty
    limits
    droppedWork := false
    live := true }

/-- A sound upper bound on proof-payload traversal for any engine-valid
reply.  It charges every candidate and suggestion and the maximum number of
equalities which may be nested below each suggestion. -/
def requiredUses (limits : Hex.Interval.State.Limits) : Nat :=
  limits.maxOutcomeCandidates +
    limits.maxOutcomeSuggestions * (limits.maxProposalItems + 1)

/-- Every engine-valid payload position may carry a distinct draft, exact
coverage bounds valid draft count by use count, and any locally valid reply
must fit an empty arena. -/
def limitsCoherent (limits : Limits) : Bool :=
  requiredUses limits.engine ≤ limits.arena.maxUses &&
    requiredUses limits.engine ≤ limits.arena.maxDrafts &&
    limits.arena.maxDrafts ≤ limits.arena.maxUses &&
    limits.arena.maxDrafts ≤ limits.arena.maxEntries &&
    limits.arena.maxDraftCells ≤ limits.arena.maxBodyCells

/-- Assemble the exact registry first, validate its signatures and package
configuration, then compile the engine and put it under policy control. -/
opaque Session.start (factDomain : FactDomain Fact) (program : Program)
    (packages : Array (Package Fact)) (facts : Array Fact) (limits : Limits)
    (scope : Hex.Interval.Policy.ScopeId := { index := 0 }) :
    Except StartError (Session Fact) :=
  match Registry.buildWithin limits.engine packages with
  | .error error => .error (.registry error)
  | .ok registry =>
      match preflightStart program registry.registrations facts.size limits.engine with
      | .error error => .error (.engine error)
      | .ok () =>
          if !registry.acceptsProgram program then
            .error .programRejected
          else if !limitsCoherent limits then
            .error .incoherentLimits
          else if !registry.acceptsLimits program limits.engine limits.arena then
            .error .limitsRejected
          else
            match Engine.start factDomain program registry.registrations facts
                limits.engine #[] registry.acceptsBinding with
            | .error error => .error (.engine error)
            | .ok engine =>
                .ok (make (Propagator.Policy.State.start engine limits.policy scope)
                  registry limits)

private def withState (session : Session Fact)
    (state : Propagator.Policy.State Fact) : Session Fact :=
  { session with state }

private def halt (session : Session Fact) (state : Propagator.Policy.State Fact)
    (registry : Registry Fact := session.registry) : Session Fact :=
  { session with state, registry, live := false }

private def commit (session : Session Fact) (state : Propagator.Policy.State Fact)
    (registry : Registry Fact) (arena : PayloadArena.Arena)
    (droppedWork : Bool := session.droppedWork) : Session Fact :=
  { session with state, registry, arena, droppedWork }

private def hasApplication (state : Propagator.Policy.State Fact) : Nat -> Bool
  | 0 => false
  | count + 1 =>
      (state.offer? (.application { index := count })).isSome ||
        hasApplication state count

private def hasEquality (state : Propagator.Policy.State Fact) : Nat -> Bool
  | 0 => false
  | count + 1 =>
      (state.offer? (.equality { index := count })).isSome ||
        hasEquality state count

private def hasNarrowingSuggestion
    (state : Propagator.Policy.State Fact) : Nat -> Bool
  | 0 => false
  | count + 1 =>
      ((state.offer? (.suggestion { index := count })).isSome &&
        (state.engine.suggestions[count]?).any fun retained =>
          Suggestion.affectsClosure retained.suggestion) ||
        hasNarrowingSuggestion state count

/-- Whether this live snapshot has reached propagation closure.  Optional
split offers do not affect closure, while any live invocation, equality,
retry, instantiation, earlier failed work, contradiction, or pending reply
prevents the claim. -/
opaque Session.complete (session : Session Fact) : Bool :=
  session.live && !session.droppedWork && !session.state.incomplete &&
    session.state.engine.pending.isNone && !session.state.engine.contradictory &&
    !hasApplication session.state session.state.applications.size &&
    !hasEquality session.state session.state.equalities.size &&
    !hasNarrowingSuggestion session.state session.state.suggestions.size

/-- A policy can select any checked offer or explicitly dismiss it. -/
inductive Choice where
  | select (selection : PolicyDecision)
  | dismiss (selection : PolicyDecision)

/-- A bounded policy view also returns the same owned session with traversal
accounting committed. -/
inductive ViewStep (Fact : Type) where
  | ready (view : PolicyView Fact Propagator.Policy.OfferId Propagator.Policy.OfferKey)
      (session : Session Fact)
  | resource (error : Propagator.Policy.ViewError) (session : Session Fact)
  | contradiction (session : Session Fact)
  | invalidSession (session : Session Fact)

/-- Obtain the next external-policy view without exposing a replaceable policy
state. -/
opaque Session.view (session : Session Fact) : ViewStep Fact :=
  if !session.live || session.state.engine.pending.isSome then
    .invalidSession session
  else if session.state.engine.contradictory then
    .contradiction session
  else
    match session.state.view with
    | .error error => .resource error { session with live := false }
    | .ok (view, state) => .ready view (withState session state)

/-- Result of one policy-owned choice.  Every successful constructor returns
the next coherent session rather than separable components. -/
inductive Step (Fact : Type) where
  | rule (selection : PolicyDecision)
      (observation : Propagator.Policy.RuleObservation Fact)
      (session : Session Fact)
  | equality (selection : PolicyDecision)
      (observation : Propagator.Policy.EqualityObservation Fact)
      (session : Session Fact)
  | instance (selection : PolicyDecision)
      (completion : Propagator.Policy.Completed) (session : Session Fact)
  | dismissed (selection : PolicyDecision) (session : Session Fact)
  | split (selection : PolicyDecision)
      (plan : Propagator.Policy.SplitPlan Fact) (session : Session Fact)
  | rejected (selection : PolicyDecision)
      (reason : Propagator.Policy.Rejection) (session : Session Fact)
  | contradiction (session : Session Fact)
  | engineResource (resource : Hex.Interval.State.Resource) (session : Session Fact)
  | factResource (budget : Nat) (session : Session Fact)
  | invalidReply (error : ReplyError) (session : Session Fact)
  | invalidPayload (error : PayloadArena.Invalid) (session : Session Fact)
  /-- A package exceeded a per-reply payload encoding bound. The failed reply
  is consumed and other independent policy choices remain available. -/
  | rejectedPayload (resource : PayloadArena.Resource) (session : Session Fact)
  /-- A whole-run payload arena bound was exhausted. -/
  | payloadResource (resource : PayloadArena.Resource) (session : Session Fact)
  | invalidSession (session : Session Fact)

private def outcomeListsBounded (limits : Hex.Interval.State.Limits) : Outcome Fact -> Bool
  | .success candidates suggestions _ =>
      listWithin limits.maxOutcomeCandidates candidates &&
        listWithin limits.maxOutcomeSuggestions suggestions
  | .noChange _ | .inapplicable | .resourceLimit _ | .failed _ => true

namespace PayloadFailureCode

/-- Stable bounded diagnostic used to clear a request whose package evidence
was malformed or exceeded a package-local encoding bound. -/
def rejected : Nat := 0

end PayloadFailureCode

private def failPayload (session : Session Fact)
    (state : Propagator.Policy.State Fact) (registry : Registry Fact)
    (action : Action) (error : PayloadArena.Invalid) : Step Fact :=
  match state.submit (action.reply (.failed PayloadFailureCode.rejected)) with
  | .accepted _ next =>
      .invalidPayload error
        (commit session next registry session.arena true)
  | .invalid replyError next =>
      .invalidReply replyError (halt session next registry)
  | .engineResource resource next =>
      .engineResource resource (halt session next registry)
  | .factResource budget next =>
      .factResource budget (halt session next registry)
  | .malformedState next =>
      .invalidSession (halt session next registry)

/-- A use, draft, draft-cell, atom, or schema excess is local to one package
reply. Consume that reply as a bounded failure, discard its prospective arena,
and preserve the live session while permanently withholding completeness. -/
private def rejectPayload (session : Session Fact)
    (state : Propagator.Policy.State Fact) (registry : Registry Fact)
    (action : Action) (resource : PayloadArena.Resource) : Step Fact :=
  match state.submit (action.reply (.failed PayloadFailureCode.rejected)) with
  | .accepted _ next =>
      .rejectedPayload resource
        (commit session next registry session.arena true)
  | .invalid replyError next =>
      .invalidReply replyError (halt session next registry)
  | .engineResource engineResource next =>
      .engineResource engineResource (halt session next registry)
  | .factResource budget next =>
      .factResource budget (halt session next registry)
  | .malformedState next =>
      .invalidSession (halt session next registry)

/-- A whole-run arena limit is fatal. Clear the selected request without
committing its prepared matcher cursor, retain no prospective arena state, and
return a non-live session which cannot later claim saturation. -/
private def exhaustPayload (session : Session Fact)
    (state : Propagator.Policy.State Fact) (registry : Registry Fact)
    (resource : PayloadArena.Resource) : Step Fact :=
  match state.abortPending with
  | some next =>
      .payloadResource resource (halt session next registry)
  | none => .invalidSession (halt session state registry)

private def rejectedSession (session : Session Fact)
    (state : Propagator.Policy.State Fact)
    (reason : Propagator.Policy.Rejection) : Session Fact :=
  match reason with
  | .decisionLimit | .actionLimit | .malformedState =>
      halt session state
  | .wrongScope | .staleSerial | .staleProgram | .missingOffer | .wrongKey =>
      withState session state

private def finishEquality (session : Session Fact)
    (selection : PolicyDecision)
    (observation : Propagator.Policy.EqualityObservation Fact)
    (state : Propagator.Policy.State Fact) : Step Fact :=
  match observation.outcome with
  | .engineResource resource =>
      .engineResource resource (halt session state)
  | .factResource budget =>
      .factResource budget (halt session state)
  | .invalid _ =>
      .invalidSession (halt session state)
  | .noChange | .improved | .contradiction =>
      .equality selection observation (withState session state)

private def submitInvocation (session : Session Fact)
    (selection : PolicyDecision)
    (request : RuleRequest Fact) (state : Propagator.Policy.State Fact)
    (invocation : Invocation Fact) (registry : Registry Fact) : Step Fact :=
  let plan := invocation.plan
  let replay := invocation.replay
  if !outcomeListsBounded session.limits.engine plan.outcome then
    match state.submit (request.action.reply plan.outcome) with
    | .accepted _ next =>
        .invalidSession (halt session next registry)
    | .invalid error next =>
        .invalidReply error (halt session next registry)
    | .engineResource resource next =>
        .engineResource resource (halt session next registry)
    | .factResource budget next =>
        .factResource budget (halt session next registry)
    | .malformedState next =>
        .invalidSession (halt session next registry)
  else
    match replay.freeze session.limits.arena session.arena request.action
        plan.outcome plan.drafts with
    | .invalid error _ =>
        failPayload session state registry request.action error
    | .resourceLimit resource _ =>
        match resource with
        | .uses | .drafts | .draftCells | .atom | .schema =>
            rejectPayload session state registry request.action resource
        | .entries | .bodyCells =>
            exhaustPayload session state registry resource
    | .ready arena outcome =>
        match state.submit (request.action.reply outcome) with
        | .accepted observation next =>
            .rule selection observation (commit session next registry arena)
        | .invalid error next =>
            .invalidReply error (halt session next registry)
        | .engineResource resource next =>
            .engineResource resource (halt session next registry)
        | .factResource budget next =>
            .factResource budget (halt session next registry)
        | .malformedState next =>
            .invalidSession (halt session next registry)

private def select (session : Session Fact)
    (selection : PolicyDecision) : Step Fact :=
  match session.state.select selection with
  | .request request state =>
      let (invocation, registry) := session.registry.invokePlanned request
      submitInvocation session selection request state invocation registry
  | .equality observation state =>
      finishEquality session selection observation state
  | .completed completion state =>
      match completion with
      | .dismissed => .invalidSession (halt session state)
      | .instanceAdmitted _ | .instanceDuplicate | .instanceRejected _ =>
          .instance selection completion (withState session state)
  | .split plan state =>
      .split selection plan (withState session state)
  | .rejected reason state =>
      .rejected selection reason (rejectedSession session state reason)
  | .engineResource resource state =>
      .engineResource resource (halt session state)
  | .factResource budget state =>
      .factResource budget (halt session state)

private def dismiss (session : Session Fact)
    (selection : PolicyDecision) : Step Fact :=
  match session.state.dismiss selection with
  | .completed .dismissed state =>
      .dismissed selection (withState session state)
  | .rejected reason state =>
      .rejected selection reason (rejectedSession session state reason)
  | .engineResource resource state =>
      .engineResource resource (halt session state)
  | .factResource budget state =>
      .factResource budget (halt session state)
  | .request _ state | .equality _ state | .completed _ state | .split _ state =>
      .invalidSession (halt session state)

/-- Execute one external-policy choice through the single proof-producing
ownership boundary. -/
opaque Session.choose (session : Session Fact) (choice : Choice) : Step Fact :=
  if !session.live || session.state.engine.pending.isSome then
    .invalidSession session
  else if session.state.engine.contradictory then
    .contradiction session
  else
    match choice with
    | .select selection => select session selection
    | .dismiss selection => dismiss session selection

end Hex.Interval.Experiment.PolicySession
