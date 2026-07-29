/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PackageRegistry

@[expose] public section

/-!
# Session-owned interval propagation and proof payloads

A session binds the checked engine, the exact function-package registry that
compiled it, and one immutable proof-payload arena. Its private constructor
prevents callers from pairing independently assembled values.

For a rule action, `advance` invokes the routed package, freezes and relocates
all reply-local proof labels prospectively, and submits the relocated outcome.
The new arena commits only when engine submission succeeds. Package caches may
still record a failed invocation because they are explicitly non-semantic;
engine facts, expression nodes, provenance, and the arena remain atomic.
Malformed package evidence is submitted to the engine as a failed rule reply:
the request latch is cleared, the session remains usable, and completeness is
permanently lost. Exceeding a package-local payload-use, draft, draft-cell,
atom, or schema bound has the same recoverable behavior. Exhausting remaining
whole-run arena entry or body capacity after earlier commits, or encountering
an engine-invalid transition, instead returns a non-live session snapshot
which cannot later be resumed and mislabeled saturated. This cumulative stop
is an intentional conservative policy for the eager prototype: an otherwise
valid selected transition could not be retained, so the session treats it like
global engine-resource exhaustion rather than skipping required work. Package
failure and unprocessed narrowing suggestions likewise make the final status
incomplete.
-/

namespace Hex.Interval.Experiment.PayloadSession

open Propagator

/-- Failure while assembling one coherent run snapshot. -/
inductive StartError where
  | registry (error : RegistryError)
  | programRejected
  | incoherentLimits
  | limitsRejected
  | engine (error : Propagator.StartError)
  deriving DecidableEq, Repr

/-- Engine, package registry, and proof arena with a private pairing
constructor. Public projections permit inspection without permitting a forged
session. -/
structure Session (Fact : Type) where
  private mk ::
  engine : Engine Fact
  registry : Registry Fact
  arena : PayloadArena.Arena
  arenaLimits : PayloadArena.Limits
  /-- Some rule or narrowing work was dropped rather than retained. -/
  droppedWork : Bool
  live : Bool

private def make (engine : Engine Fact) (registry : Registry Fact)
    (arenaLimits : PayloadArena.Limits) : Session Fact :=
  { engine
    registry
    arena := .empty
    arenaLimits
    droppedWork := false
    live := true }

/-- A sound upper bound on payload-arena work in any engine-valid reply:
every candidate, every suggestion constructor, and at most
`maxProposalItems` nested equalities for each suggestion. -/
def requiredUses (limits : Propagator.Limits) : Nat :=
  limits.maxOutcomeCandidates +
    limits.maxOutcomeSuggestions * (limits.maxProposalItems + 1)

/-- The count envelope admits one distinct draft for every engine-valid
payload use. `maxDrafts ≤ maxUses` also bounds malformed pre-coverage draft
lists by the use-traversal envelope, while the local draft and cell caps must
fit an empty arena. Therefore only capacity consumed by earlier commits can
produce a whole-run exhaustion. -/
def limitsCoherent (limits : Propagator.Limits)
    (arenaLimits : PayloadArena.Limits) : Bool :=
  requiredUses limits ≤ arenaLimits.maxDrafts &&
    arenaLimits.maxDrafts ≤ arenaLimits.maxUses &&
    arenaLimits.maxDrafts ≤ arenaLimits.maxEntries &&
    arenaLimits.maxDraftCells ≤ arenaLimits.maxBodyCells

/-- Bound package metadata, compile and validate the engine-owned program,
then run package-specific program checks and start with an empty proof arena.
The generic engine preflight precedes any package callback which may traverse
the program. -/
opaque Session.start (factDomain : FactDomain Fact) (program : Program)
    (packages : Array (Package Fact)) (facts : Array Fact)
    (limits : Propagator.Limits) (arenaLimits : PayloadArena.Limits) :
    Except StartError (Session Fact) :=
  match Registry.buildWithin limits packages with
  | .error error => .error (.registry error)
  | .ok registry =>
      if !limitsCoherent limits arenaLimits then
        .error .incoherentLimits
      else
        match Engine.start factDomain program registry.registrations facts limits with
        | .error error => .error (.engine error)
        | .ok engine =>
            if !registry.acceptsProgram program then
              .error .programRejected
            else if !registry.acceptsLimits program limits arenaLimits then
              .error .limitsRejected
            else
              .ok (make engine registry arenaLimits)

/-- Result of one session-owned rule or equality transition. -/
inductive Step (Fact : Type) where
  | advanced (session : Session Fact)
  | saturated (session : Session Fact)
  | incomplete (session : Session Fact)
  | contradiction (session : Session Fact)
  | engineResource (resource : Propagator.Resource) (session : Session Fact)
  | factResource (budget : Nat) (session : Session Fact)
  | invalidReply (error : ReplyError) (session : Session Fact)
  | invalidPayload (error : PayloadArena.Invalid) (session : Session Fact)
  /-- A package exceeded a per-reply payload encoding bound. The failed reply
  is consumed and other independent work may continue. -/
  | rejectedPayload (resource : PayloadArena.Resource) (session : Session Fact)
  /-- An otherwise valid reply exhausted a cumulative arena bound. The eager
  session intentionally stops instead of skipping selected required work. -/
  | payloadResource (resource : PayloadArena.Resource) (session : Session Fact)
  | invalidEngine (session : Session Fact)

private def withEngine (session : Session Fact) (engine : Engine Fact) :
    Session Fact :=
  { session with engine }

private def haltEngine (session : Session Fact) (engine : Engine Fact) :
    Session Fact :=
  { session with engine, live := false }

private def haltRegistry (session : Session Fact) (engine : Engine Fact)
    (registry : Registry Fact) : Session Fact :=
  { session with engine, registry, live := false }

private def commit (session : Session Fact) (engine : Engine Fact)
    (registry : Registry Fact) (arena : PayloadArena.Arena)
    (droppedWork : Bool) : Session Fact :=
  { session with engine, registry, arena, droppedWork }

/-- Whether the session still has all work required for a propagation fixed
point. This deliberately covers fatal snapshots, previously dropped work, and
retained narrowing suggestions; callers need not reconstruct those conditions
from public projections. -/
def Session.complete (session : Session Fact) : Bool :=
  session.live && !session.droppedWork &&
    !session.engine.suggestions.any fun retained =>
      retained.suggestion.affectsClosure

/-- Negative package outcomes which explicitly abandon required rule work.
Suggestion loss is taken from the engine-returned admission plan instead. -/
private def outcomeDropsWork : Outcome Fact -> Bool
  | .resourceLimit _ | .failed _ => true
  | .success _ _ _ | .noChange _ | .inapplicable => false

/-- Check the two outer reply lists using the engine's own trusted bounds
before the arena traverses payload uses or drafts. Nested instantiation lists
remain bounded by the arena cap here and by `maxProposalItems` during engine
admission. -/
private def outcomeListsBounded (limits : Propagator.Limits) : Outcome Fact -> Bool
  | .success candidates suggestions _ =>
      listWithin limits.maxOutcomeCandidates candidates &&
        listWithin limits.maxOutcomeSuggestions suggestions
  | .noChange _ | .inapplicable | .resourceLimit _ | .failed _ => true

namespace PayloadFailureCode

/-- Stable engine diagnostic for a package plan rejected before semantic
admission, whether for malformed drafts or a per-reply encoding bound. Zero is
valid under every diagnostic limit. -/
def rejected : Nat := 0

end PayloadFailureCode

/-- Clear a malformed package reply through the ordinary engine protocol.
The typed payload error remains visible in the one-step result, while bounded
drivers continue the live session and ultimately report incompleteness. -/
private def failPayload (session : Session Fact) (engine : Engine Fact)
    (registry : Registry Fact) (action : Action)
    (error : PayloadArena.Invalid) : Step Fact :=
  match engine.submit (action.reply (.failed PayloadFailureCode.rejected)) with
  | .accepted _ next =>
      .invalidPayload error
        (commit session next registry session.arena true)
  | .invalid replyError next =>
      .invalidReply replyError (haltRegistry session next registry)
  | .resourceLimit resource next =>
      .engineResource resource (haltRegistry session next registry)
  | .factResourceLimit budget next =>
      .factResource budget (haltRegistry session next registry)

/-- Treat a package-local payload bound violation like malformed package
evidence: consume a bounded failed reply, retain no prospective arena entries,
continue independent work, and permanently withhold completeness. -/
private def rejectPayload (session : Session Fact) (engine : Engine Fact)
    (registry : Registry Fact) (action : Action)
    (resource : PayloadArena.Resource) : Step Fact :=
  match engine.submit (action.reply (.failed PayloadFailureCode.rejected)) with
  | .accepted _ next =>
      .rejectedPayload resource
        (commit session next registry session.arena true)
  | .invalid replyError next =>
      .invalidReply replyError (haltRegistry session next registry)
  | .resourceLimit engineResource next =>
      .engineResource engineResource (haltRegistry session next registry)
  | .factResourceLimit budget next =>
      .factResource budget (haltRegistry session next registry)

/-- Run one checked transition. A prospective arena is discarded for every
engine rejection or resource refusal. -/
opaque Session.advance (session : Session Fact) : Step Fact :=
  if !session.live then
    .invalidEngine session
  else match session.engine.poll with
  | .request request engine =>
      let (plan, registry) := session.registry.invokePlanned request
      if !outcomeListsBounded engine.limits plan.outcome then
        match engine.submit (request.action.reply plan.outcome) with
        | .accepted _ _ =>
            -- Defensive against validation drift: never retain an unfrozen
            -- accepted outcome from this pre-screen rejection path.
            .invalidEngine (haltRegistry session engine.finishReply registry)
        | .invalid error next =>
            .invalidReply error (haltRegistry session next registry)
        | .resourceLimit resource next =>
            .engineResource resource (haltRegistry session next registry)
        | .factResourceLimit budget next =>
            .factResource budget (haltRegistry session next registry)
      else
        match PayloadArena.freeze session.arenaLimits session.arena request.action
            plan.outcome plan.drafts with
        | .invalid error _ =>
            failPayload session engine registry request.action error
        | .resourceLimit resource _ =>
            match resource with
            | .uses | .drafts | .draftCells | .atom | .schema =>
                rejectPayload session engine registry request.action resource
            | .entries | .bodyCells =>
                .payloadResource resource
                  (haltRegistry session engine.finishReply registry)
        | .ready arena outcome =>
            match engine.submit (request.action.reply outcome) with
            | .accepted admission next =>
                .advanced
                  (commit session next registry arena
                    (session.droppedWork || outcomeDropsWork outcome ||
                      admission.affectsClosure))
            | .invalid error next =>
                .invalidReply error (haltRegistry session next registry)
            | .resourceLimit resource next =>
                .engineResource resource (haltRegistry session next registry)
            | .factResourceLimit budget next =>
                .factResource budget (haltRegistry session next registry)
  | .equality equality engine =>
      match engine.contractEquality equality with
      | .advanced _ next => .advanced (withEngine session next)
      | .invalid _ _ next => .invalidEngine (haltEngine session next)
      | .resourceLimit resource _ next =>
          .engineResource resource (haltEngine session next)
      | .factResourceLimit budget _ next =>
          .factResource budget (haltEngine session next)
  | .saturated engine =>
      let session := withEngine session engine
      if session.complete then
        .saturated session
      else
        .incomplete session
  | .contradiction engine => .contradiction (withEngine session engine)
  | .resourceLimit resource engine =>
      .engineResource resource (haltEngine session engine)
  | .awaitingReply engine | .invalidState engine =>
      .invalidEngine (haltEngine session engine)

/-- Why a bounded session run stopped. -/
inductive Stop where
  | saturated
  | incomplete
  | contradiction
  | engineResource (resource : Propagator.Resource)
  | factResource (budget : Nat)
  | invalidReply (error : ReplyError)
  | payloadResource (resource : PayloadArena.Resource)
  | invalidEngine
  | driverFuel
  deriving DecidableEq, Repr

structure Run (Fact : Type) where
  private mk ::
  session : Session Fact
  stop : Stop

private def runSteps : Nat -> Session Fact -> Run Fact
  | 0, session => { session, stop := .driverFuel }
  | fuel + 1, session =>
      match session.advance with
      | .advanced next => runSteps fuel next
      | .saturated next => { session := next, stop := .saturated }
      | .incomplete next => { session := next, stop := .incomplete }
      | .contradiction next => { session := next, stop := .contradiction }
      | .engineResource resource next =>
          { session := next, stop := .engineResource resource }
      | .factResource budget next =>
          { session := next, stop := .factResource budget }
      | .invalidReply error next =>
          { session := next, stop := .invalidReply error }
      | .invalidPayload _ next => runSteps fuel next
      | .rejectedPayload _ next => runSteps fuel next
      | .payloadResource resource next =>
          { session := next, stop := .payloadResource resource }
      | .invalidEngine next => { session := next, stop := .invalidEngine }

/-- Bounded FIFO execution through the session-owned evidence transaction. -/
opaque Session.drive (fuel : Nat) (session : Session Fact) : Run Fact :=
  runSteps fuel session

end Hex.Interval.Experiment.PayloadSession
