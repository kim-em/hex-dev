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
Malformed or resource-failed transitions return a non-live session snapshot
which cannot later be resumed and mislabeled saturated. Package failure and
unprocessed narrowing suggestions likewise make the final status incomplete.
-/

namespace Hex.Interval.Experiment.PayloadSession

open Propagator

/-- Failure while assembling one coherent run snapshot. -/
inductive StartError where
  | registry (error : RegistryError)
  | programRejected
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
  incomplete : Bool
  live : Bool

private def make (engine : Engine Fact) (registry : Registry Fact)
    (arenaLimits : PayloadArena.Limits) : Session Fact :=
  { engine
    registry
    arena := .empty
    arenaLimits
    incomplete := false
    live := true }

/-- Validate package metadata and signatures before compiling the engine, then
start with an empty proof arena. -/
opaque Session.start (factDomain : FactDomain Fact) (program : Program)
    (packages : Array (Package Fact)) (facts : Array Fact)
    (limits : Propagator.Limits) (arenaLimits : PayloadArena.Limits) :
    Except StartError (Session Fact) :=
  match Registry.buildWithin limits packages with
  | .error error => .error (.registry error)
  | .ok registry =>
      if !registry.acceptsProgram program then
        .error .programRejected
      else if !registry.acceptsLimits program limits then
        .error .limitsRejected
      else
        match Engine.start factDomain program registry.registrations facts limits with
        | .error error => .error (.engine error)
        | .ok engine => .ok (make engine registry arenaLimits)

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
  | payloadResource (resource : PayloadArena.Resource) (session : Session Fact)
  | invalidEngine (session : Session Fact)

private def withEngine (session : Session Fact) (engine : Engine Fact) :
    Session Fact :=
  { session with engine }

private def withRegistry (session : Session Fact) (engine : Engine Fact)
    (registry : Registry Fact) : Session Fact :=
  { session with engine, registry }

private def haltEngine (session : Session Fact) (engine : Engine Fact) :
    Session Fact :=
  { session with engine, live := false }

private def haltRegistry (session : Session Fact) (engine : Engine Fact)
    (registry : Registry Fact) : Session Fact :=
  { session with engine, registry, live := false }

private def commit (session : Session Fact) (engine : Engine Fact)
    (registry : Registry Fact) (arena : PayloadArena.Arena)
    (incomplete : Bool) : Session Fact :=
  { session with engine, registry, arena, incomplete }

private def narrows : Suggestion -> Bool
  | .retry _ | .instantiate _ => true
  | .split _ => false

private def retainedNarrowing (engine : Engine Fact) : Bool :=
  engine.suggestions.any fun retained => narrows retained.suggestion

private def outcomeIncomplete (engine : Engine Fact) : Outcome Fact -> Bool
  | .resourceLimit _ | .failed _ => true
  | .success _ suggestions _ =>
      let room := engine.limits.maxRetainedSuggestions - engine.suggestions.size
      (suggestions.drop room).any narrows
  | .noChange _ | .inapplicable => false

/-- Run one checked transition. A prospective arena is discarded for every
engine rejection or resource refusal. -/
opaque Session.advance (session : Session Fact) : Step Fact :=
  if !session.live then
    .invalidEngine session
  else match session.engine.poll with
  | .request request engine =>
      let (plan, registry) := session.registry.invokePlanned request
      match PayloadArena.freeze session.arenaLimits session.arena request.action
          plan.outcome plan.drafts with
      | .invalid error _ =>
          .invalidPayload error
            (haltRegistry session engine.finishReply registry)
      | .resourceLimit resource _ =>
          .payloadResource resource
            (haltRegistry session engine.finishReply registry)
      | .ready arena outcome =>
          match engine.submit (request.action.reply outcome) with
          | .accepted next =>
              .advanced
                (commit session next registry arena
                  (session.incomplete || outcomeIncomplete engine outcome))
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
      if session.incomplete || retainedNarrowing engine then
        .incomplete session
      else
        .saturated session
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
  | invalidPayload (error : PayloadArena.Invalid)
  | payloadResource (resource : PayloadArena.Resource)
  | invalidEngine
  | driverFuel
  deriving DecidableEq, Repr

structure Run (Fact : Type) where
  session : Session Fact
  stop : Stop

/-- Bounded FIFO execution through the session-owned evidence transaction. -/
def Session.drive : Nat -> Session Fact -> Run Fact
  | 0, session => { session, stop := .driverFuel }
  | fuel + 1, session =>
      match session.advance with
      | .advanced next => next.drive fuel
      | .saturated next => { session := next, stop := .saturated }
      | .incomplete next => { session := next, stop := .incomplete }
      | .contradiction next => { session := next, stop := .contradiction }
      | .engineResource resource next =>
          { session := next, stop := .engineResource resource }
      | .factResource budget next =>
          { session := next, stop := .factResource budget }
      | .invalidReply error next =>
          { session := next, stop := .invalidReply error }
      | .invalidPayload error next =>
          { session := next, stop := .invalidPayload error }
      | .payloadResource resource next =>
          { session := next, stop := .payloadResource resource }
      | .invalidEngine next => { session := next, stop := .invalidEngine }

end Hex.Interval.Experiment.PayloadSession
