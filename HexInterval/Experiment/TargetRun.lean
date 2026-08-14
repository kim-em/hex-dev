/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Target-directed policy runs

This experiment drives the proof-producing policy-session boundary until the
current fact entails a requested target, propagation saturates, the external
policy stops, a split is prepared, or a resource is exhausted.  The controller
is independent of the fact representation and operation packages.  It sees a
bounded policy view and may keep arbitrary private state while choosing among
the engine's checked offers.

Target detection is only a search stopping condition.  It applies the fact
domain's `narrow` operation to the current and requested facts; proof emission
must still resolve the returned version and replay a kernel-checked subsumption
step.  A faulty controller or target check can therefore cause failure or extra
work, but cannot establish a theorem.
-/

namespace Hex.Interval.Experiment.TargetRun

open Propagator PolicySession

/-- One external policy decision.  The driver fills in the view identity and
uses the chosen offer's complete semantic key when constructing a selection. -/
inductive Decision (PolicyState : Type)
  | select (offer : Propagator.Policy.OfferView) (next : PolicyState)
  | dismiss (offer : Propagator.Policy.OfferView) (next : PolicyState)
  | stop (next : PolicyState)

/-- Observations delivered back to the external policy in execution order. -/
inductive Event (Fact : Type)
  | rule (observation : Propagator.Policy.RuleObservation Fact)
  | equality (observation : Propagator.Policy.EqualityObservation Fact)
  | instance (completion : Propagator.Policy.Completed)
  | dismissed
  | rejected (reason : Propagator.Policy.Rejection)
  | invalidPayload (error : PayloadArena.Invalid)
  | rejectedPayload (resource : PayloadArena.Resource)

/-- An arbitrary upgradeable policy over bounded engine-owned views. -/
structure Controller (Fact PolicyState : Type) where
  update : PolicyState -> Event Fact -> PolicyState
  choose : PolicyState -> Propagator.Policy.View Fact -> Decision PolicyState

/-- The exact retained fact version which triggered target stopping. -/
structure Reached (Fact : Type) where
  seen : SeenVersion
  fact : Fact

/-- Why a target-directed run stopped. -/
inductive Stop (Fact : Type)
  | target (reached : Reached Fact)
  | saturated
  | contradiction
  | split (plan : Propagator.Policy.SplitPlan Fact)
  | policyStop (liveOffers : Nat)
  | incomplete
  | viewResource (error : Propagator.Policy.ViewError)
  | engineResource (resource : Propagator.Resource)
  | factResource (budget : Nat)
  | payloadResource (resource : PayloadArena.Resource)
  | invalidReply (error : ReplyError)
  | invalidPayload (error : PayloadArena.Invalid)
  | rejected (reason : Propagator.Policy.Rejection)
  | invalidSession
  | fuel

/-- A run retains the single coherent proof-producing session, arbitrary
policy state, all delivered observations, and its precise stopping reason. -/
structure Result (Fact PolicyState : Type) where
  session : Session Fact
  policyState : PolicyState
  events : Array (Event Fact)
  stop : Stop Fact

def selection (view : Propagator.Policy.View Fact)
    (offer : Propagator.Policy.OfferView) : Propagator.Policy.Selection :=
  { scope := view.scope
    serial := view.serial
    programVersion := view.programVersion
    id := offer.id
    expected := offer.key }

/-- Check whether the installed fact entails the requested target.  This is a
runtime search test, not proof evidence. -/
def reached? (domain : FactDomain Fact) (target : NodeId) (requested : Fact)
    (session : Session Fact) : Option (Reached Fact) := do
  let instruction <- session.state.engine.program.node? target
  let current <- session.state.engine.facts[target.index]?
  let version <- session.state.engine.versions[target.index]?
  match domain.narrow instruction.domain current requested with
  | .noChange => some { seen := { node := target, version }, fact := current }
  | .improved _ | .contradiction _ | .malformed _ | .resourceLimit _ => none

def record (controller : Controller Fact PolicyState) (event : Event Fact)
    (policyState : PolicyState) (events : Array (Event Fact)) :
    PolicyState × Array (Event Fact) :=
  (controller.update policyState event, events.push event)

def finish (session : Session Fact) (policyState : PolicyState)
    (events : Array (Event Fact)) (stop : Stop Fact) : Result Fact PolicyState :=
  { session, policyState, events, stop }

/-- Consume one policy-session transition.  Recoverable outcomes call the
supplied continuation; terminal outcomes retain the coherent returned session. -/
def continueWith (controller : Controller Fact PolicyState)
    (resume : Session Fact -> PolicyState -> Array (Event Fact) -> Result Fact PolicyState)
    (policyState : PolicyState) (events : Array (Event Fact))
    (step : PolicySession.Step Fact) : Result Fact PolicyState :=
  match step with
  | .rule _ observation session =>
      let (policyState, events) :=
        record controller (.rule observation) policyState events
      resume session policyState events
  | .equality _ observation session =>
      let (policyState, events) :=
        record controller (.equality observation) policyState events
      resume session policyState events
  | .instance _ completion session =>
      let (policyState, events) :=
        record controller (.instance completion) policyState events
      resume session policyState events
  | .dismissed _ session =>
      let (policyState, events) := record controller .dismissed policyState events
      resume session policyState events
  | .split _ plan session => finish session policyState events (.split plan)
  | .rejected _ reason session =>
      let (policyState, events) :=
        record controller (.rejected reason) policyState events
      if session.live then
        resume session policyState events
      else
        finish session policyState events (.rejected reason)
  | .contradiction session => finish session policyState events .contradiction
  | .engineResource resource session =>
      finish session policyState events (.engineResource resource)
  | .factResource budget session =>
      finish session policyState events (.factResource budget)
  | .invalidReply error session =>
      finish session policyState events (.invalidReply error)
  | .invalidPayload error session =>
      let (policyState, events) :=
        record controller (.invalidPayload error) policyState events
      if session.live then
        resume session policyState events
      else
        finish session policyState events (.invalidPayload error)
  | .rejectedPayload resource session =>
      let (policyState, events) :=
        record controller (.rejectedPayload resource) policyState events
      resume session policyState events
  | .payloadResource resource session =>
      finish session policyState events (.payloadResource resource)
  | .invalidSession session => finish session policyState events .invalidSession

/-- Execute a bounded external policy from one coherent proof-producing
session.  Split plans are returned to the caller; branch creation is a later
layer. -/
def driveFrom (domain : FactDomain Fact) (target : NodeId) (requested : Fact)
    (controller : Controller Fact PolicyState) :
    Nat -> Session Fact -> PolicyState -> Array (Event Fact) -> Result Fact PolicyState
  | fuel, session, policyState, events =>
      if session.state.engine.contradictory then
        finish session policyState events .contradiction
      else
        match reached? domain target requested session with
        | some reached => finish session policyState events (.target reached)
        | none =>
            match session.view with
            | .resource error next =>
                finish next policyState events (.viewResource error)
            | .contradiction next =>
                finish next policyState events .contradiction
            | .invalidSession next =>
                finish next policyState events .invalidSession
            | .ready view viewed =>
                if view.offers.isEmpty then
                  if viewed.complete then
                    finish viewed policyState events .saturated
                  else
                    finish viewed policyState events .incomplete
                else
                  match fuel with
                  | 0 => finish viewed policyState events .fuel
                  | remaining + 1 =>
                      let decision := controller.choose policyState view
                      match decision with
                      | .stop next =>
                          finish viewed next events (.policyStop view.offers.size)
                      | .select offer next =>
                          continueWith controller
                            (driveFrom domain target requested controller remaining) next events
                            (viewed.choose (.select (selection view offer)))
                      | .dismiss offer next =>
                          continueWith controller
                            (driveFrom domain target requested controller remaining) next events
                            (viewed.choose (.dismiss (selection view offer)))

termination_by fuel => fuel

/-- Start a target-directed run with an empty policy-observation stream. -/
def drive (domain : FactDomain Fact) (target : NodeId) (requested : Fact)
    (controller : Controller Fact PolicyState) (fuel : Nat)
    (session : Session Fact) (policyState : PolicyState) : Result Fact PolicyState :=
  driveFrom domain target requested controller fuel session policyState #[]

end Hex.Interval.Experiment.TargetRun
