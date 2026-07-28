/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Policy

@[expose] public section

/-!
# External driver for engine-owned interval-policy offers

This module connects an arbitrary external search policy and an arbitrary
external rule registry to `Policy.State`.  The policy sees only bounded views
and returns `select`, `dismiss`, or `stop`; `Policy.State` remains the sole
authority which freezes rule actions, contracts equalities, admits expression
instances, and prepares split plans.

Every completed transition is delivered to the policy and retained in one
ordered typed event stream.  The driver does not branch on a split plan.  It
returns that plan to the caller, which will eventually own proof-scope
creation.
-/

namespace Hex.Interval.Experiment.Propagator.Policy.Driver

/-! ## External policy protocol -/

/-- One external policy decision.  Policy-private state has an arbitrary Lean
type and remains outside the trusted engine. -/
inductive Step (PolicyState : Type)
  | select (selection : Selection) (next : PolicyState)
  | dismiss (selection : Selection) (next : PolicyState)
  | stop (next : PolicyState)

/-- Outcome of selecting one retained instantiation offer. -/
inductive InstanceOutcome
  | admitted (newNodes : List NodeId)
  | duplicate
  | rejected (error : AdmissionError)
  deriving Repr

/-- The engine transition which exhausted a resource. -/
inductive ResourceOrigin
  | choice (selection : Selection)
  | invocation (selection : Selection) (invocation : InvocationKey)

/-- One ordered policy observation.  Successful choices retain the exact
selection as well as the engine-produced semantic observation. -/
inductive Event (Fact : Type)
  | rule (selection : Selection) (observation : RuleObservation Fact)
  | replyRejected (selection : Selection) (invocation : InvocationKey)
      (error : ReplyError)
  | equality (selection : Selection) (observation : EqualityObservation Fact)
  | instance (selection : Selection) (outcome : InstanceOutcome)
  | dismissal (selection : Selection) (halts : Bool) (causesIncomplete : Bool)
  | splitPrepared (selection : Selection) (plan : SplitPlan Fact)
  | choiceRejected (selection : Selection) (reason : Rejection)
  | engineResource (origin : ResourceOrigin) (resource : Resource)
  | factResource (origin : ResourceOrigin) (budget : Nat)
  | decisionResource
  | viewResource (error : ViewError)
  | policyStop (liveOffers : Nat)
  | saturated
  | contradiction
  | incomplete
  | invalidState
  | driverFuel

/-- A policy learns from the same single ordered stream returned by the
driver.  Neither callback is required to terminate; failure of arbitrary
external code cannot establish a theorem. -/
structure Controller (Fact PolicyState : Type) where
  key : PolicyKey
  update : PolicyState -> Event Fact -> PolicyState
  choose : PolicyState -> View Fact -> Step PolicyState

/-! ## Driver result -/

inductive UnknownReason
  | policyStop (liveOffers : Nat)
  | requiredDismissal (selection : Selection)
  | incomplete

/-- Why policy execution stopped.  A prepared split is returned rather than
executed, and `unknown` is distinct from a genuine empty-frontier fixed point. -/
inductive Stop (Fact : Type)
  | saturated
  | contradiction
  | split (plan : SplitPlan Fact)
  | unknown (reason : UnknownReason)
  | engineResource (resource : Resource)
  | factResource (budget : Nat)
  | decisionResource
  | viewResource (error : ViewError)
  | invalidReply (error : ReplyError)
  | invalidState
  | driverFuel

/-- A run returns both kinds of arbitrary external state and the exact ordered
event stream delivered to the policy. -/
structure Result (Fact Cache PolicyState : Type) where
  state : State Fact
  policy : PolicyKey
  cache : Cache
  policyState : PolicyState
  events : Array (Event Fact)
  stop : Stop Fact

def emit (controller : Controller Fact PolicyState) (event : Event Fact)
    (policyState : PolicyState) (events : Array (Event Fact)) :
    PolicyState × Array (Event Fact) :=
  (controller.update policyState event, events.push event)

def finish (controller : Controller Fact PolicyState) (event : Event Fact)
    (stop : Stop Fact) (state : State Fact) (cache : Cache)
    (policyState : PolicyState) (events : Array (Event Fact)) :
    Result Fact Cache PolicyState :=
  let (policyState, events) := emit controller event policyState events
  { state, policy := controller.key, cache, policyState, events, stop }

def dismissalHalts : OfferId -> Bool
  | .application _ | .equality _ => true
  | .suggestion _ => false

def dismissalAffects : OfferClass -> Bool
  | .invoke | .equality | .retry | .instantiate => true
  | .split => false

/-- Whether this dismissal is responsible for completeness being unavailable.
The offer class remains visible even if an earlier transition had already
made the state incomplete. -/
def dismissalCauses (before : State Fact) (selection : Selection)
    (after : State Fact) : Bool :=
  after.incomplete &&
    (!before.incomplete || dismissalAffects selection.expected.offerClass)

def invocationOfRequest (scope : ScopeId) (request : RuleRequest Fact) : InvocationKey :=
  invocationOfAction scope request.action

/-! ## Ordered execution -/

/-- Internal fuelled loop.  The only action passed to the registry comes from
`State.select`; the driver merely echoes it through `Action.reply`. -/
def driveFrom (controller : Controller Fact PolicyState)
    (invoke : Cache -> RuleRequest Fact -> Outcome Fact × Cache) :
    Nat -> State Fact -> Cache -> PolicyState -> Array (Event Fact) ->
      Result Fact Cache PolicyState
  | fuel, state, cache, policyState, events =>
      if state.engine.pending.isSome then
        finish controller .invalidState .invalidState state cache policyState events
      else if state.engine.contradictory then
        finish controller .contradiction .contradiction state cache policyState events
      else
        match fuel with
        | 0 =>
            match state.view with
            | .error error =>
                finish controller (.viewResource error) (.viewResource error)
                  state cache policyState events
            | .ok (view, viewed) =>
                if view.offers.isEmpty then
                  if viewed.incomplete then
                    finish controller .incomplete (.unknown .incomplete)
                      viewed cache policyState events
                  else
                    finish controller .saturated .saturated viewed cache policyState events
                else if viewed.limits.maxDecisions <= viewed.metrics.decisions then
                  finish controller .decisionResource .decisionResource
                    viewed cache policyState events
                else
                  finish controller .driverFuel .driverFuel viewed cache policyState events
        | remaining + 1 =>
            match state.view with
            | .error error =>
                finish controller (.viewResource error) (.viewResource error)
                  state cache policyState events
            | .ok (view, viewed) =>
                if view.offers.isEmpty then
                  if viewed.incomplete then
                    finish controller .incomplete (.unknown .incomplete)
                      viewed cache policyState events
                  else
                    finish controller .saturated .saturated viewed cache policyState events
                else if viewed.limits.maxDecisions <= viewed.metrics.decisions then
                  finish controller .decisionResource .decisionResource
                    viewed cache policyState events
                else
                  match controller.choose policyState view with
                  | .select selection next =>
                      match viewed.select selection with
                      | .request request awaiting =>
                          let invocation := invocationOfRequest awaiting.scope request
                          let (outcome, cache) := invoke cache request
                          let reply := request.action.reply outcome
                          match awaiting.submit reply with
                          | .accepted observation afterReply =>
                              let (next, events) := emit controller
                                (.rule selection observation) next events
                              driveFrom controller invoke remaining afterReply cache next events
                          | .invalid error afterReply =>
                              finish controller
                                (.replyRejected selection invocation error) (.invalidReply error)
                                afterReply cache next events
                          | .engineResource resource afterReply =>
                              finish controller
                                (.engineResource (.invocation selection invocation) resource)
                                (.engineResource resource) afterReply cache next events
                          | .factResource budget afterReply =>
                              finish controller
                                (.factResource (.invocation selection invocation) budget)
                                (.factResource budget) afterReply cache next events
                          | .malformedState afterReply =>
                              finish controller .invalidState .invalidState
                                afterReply cache next events
                      | .equality observation afterEquality =>
                          let (next, events) := emit controller
                            (.equality selection observation) next events
                          match observation.outcome with
                          | .invalid _ =>
                              finish controller .invalidState .invalidState
                                afterEquality cache next events
                          | .noChange | .improved | .contradiction =>
                              driveFrom controller invoke remaining afterEquality cache next events
                          | .engineResource resource =>
                              finish controller
                                (.engineResource (.choice selection) resource)
                                (.engineResource resource) afterEquality cache next events
                          | .factResource budget =>
                              finish controller (.factResource (.choice selection) budget)
                                (.factResource budget) afterEquality cache next events
                      | .completed completion afterCompletion =>
                          match completion with
                          | .instanceAdmitted nodes =>
                              let (next, events) := emit controller
                                (.instance selection (.admitted nodes)) next events
                              driveFrom controller invoke remaining afterCompletion cache next
                                events
                          | .instanceDuplicate =>
                              let (next, events) := emit controller
                                (.instance selection .duplicate) next events
                              driveFrom controller invoke remaining afterCompletion cache next
                                events
                          | .instanceRejected error =>
                              let (next, events) := emit controller
                                (.instance selection (.rejected error)) next events
                              driveFrom controller invoke remaining afterCompletion cache next
                                events
                          | .dismissed =>
                              finish controller .invalidState .invalidState
                                afterCompletion cache next events
                      | .split plan afterSplit =>
                          finish controller (.splitPrepared selection plan) (.split plan)
                            afterSplit cache next events
                      | .rejected reason afterRejection =>
                          let (next, events) := emit controller
                            (.choiceRejected selection reason) next events
                          match reason with
                          | .decisionLimit =>
                              finish controller .decisionResource .decisionResource
                                afterRejection cache next events
                          | .actionLimit =>
                              finish controller
                                (.engineResource (.choice selection) .actions)
                                (.engineResource .actions) afterRejection cache next events
                          | .malformedState =>
                              finish controller .invalidState .invalidState
                                afterRejection cache next events
                          | .wrongScope | .staleSerial | .staleProgram |
                              .missingOffer | .wrongKey =>
                              driveFrom controller invoke remaining afterRejection cache next events
                      | .engineResource resource afterResource =>
                          finish controller (.engineResource (.choice selection) resource)
                            (.engineResource resource) afterResource cache next events
                      | .factResource budget afterResource =>
                          finish controller (.factResource (.choice selection) budget)
                            (.factResource budget) afterResource cache next events
                  | .dismiss selection next =>
                      match viewed.dismiss selection with
                      | .completed .dismissed afterDismissal =>
                          let halts := dismissalHalts selection.id
                          let causesIncomplete :=
                            dismissalCauses viewed selection afterDismissal
                          let (next, events) := emit controller
                            (.dismissal selection halts causesIncomplete) next events
                          if halts then
                            { state := afterDismissal
                              policy := controller.key
                              cache
                              policyState := next
                              events
                              stop := .unknown (.requiredDismissal selection) }
                          else
                            driveFrom controller invoke remaining afterDismissal cache next events
                      | .rejected reason afterRejection =>
                          let (next, events) := emit controller
                            (.choiceRejected selection reason) next events
                          match reason with
                          | .decisionLimit =>
                              finish controller .decisionResource .decisionResource
                                afterRejection cache next events
                          | .actionLimit =>
                              finish controller
                                (.engineResource (.choice selection) .actions)
                                (.engineResource .actions) afterRejection cache next events
                          | .malformedState =>
                              finish controller .invalidState .invalidState
                                afterRejection cache next events
                          | .wrongScope | .staleSerial | .staleProgram |
                              .missingOffer | .wrongKey =>
                              driveFrom controller invoke remaining afterRejection cache next events
                      | .request _ invalid | .equality _ invalid | .completed _ invalid |
                          .split _ invalid | .engineResource _ invalid |
                          .factResource _ invalid =>
                              finish controller .invalidState .invalidState
                                invalid cache next events
                  | .stop next =>
                      finish controller (.policyStop view.offers.size)
                        (.unknown (.policyStop view.offers.size)) viewed cache next events

/-- Run an external policy and registry from one policy-controlled engine
snapshot. -/
def drive (controller : Controller Fact PolicyState)
    (invoke : Cache -> RuleRequest Fact -> Outcome Fact × Cache)
    (fuel : Nat) (state : State Fact) (cache : Cache)
    (policyState : PolicyState) : Result Fact Cache PolicyState :=
  driveFrom controller invoke fuel state cache policyState #[]

end Hex.Interval.Experiment.Propagator.Policy.Driver
