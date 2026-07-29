/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PolicyDriver
import HexInterval.PolicyConformance

/-!
Conformance canaries for the external policy driver.

The underlying fixture uses opaque `f` and `g` operations over synthetic
facts.  These tests concern policy protocol semantics, not rational
arithmetic: two schedules must produce the same fixed facts, while the event
stream records their different causal histories exactly.
-/

namespace Hex.Interval.PolicyDriverConformance

open Experiment.Propagator
open Experiment.Propagator.Policy
open Experiment.Propagator.Policy.Driver
open PolicyConformance

/-! # A deterministic scripted policy -/

inductive Command
  | select (id : OfferId)
  | dismiss (id : OfferId)
  | wrongRetry (id : SuggestionId) (effort : Nat)
  | stale (id : OfferId)
  | stop

def findOffer? (view : View Fact) (id : OfferId) : Option OfferView :=
  view.offers.toList.find? fun offer => offer.id == id

def selection? (view : View Fact) (id : OfferId) : Option Selection := do
  let offer <- findOffer? view id
  some
    { scope := view.scope
      serial := view.serial
      programVersion := view.programVersion
      id
      expected := offer.key }

def choose : List Command -> View Rank -> Step (List Command)
  | [], _ => .stop []
  | .stop :: rest, _ => .stop rest
  | .select id :: rest, view =>
      match selection? view id with
      | some selection => .select selection rest
      | none => .stop rest
  | .dismiss id :: rest, view =>
      match selection? view id with
      | some selection => .dismiss selection rest
      | none => .stop rest
  | .wrongRetry id effort :: rest, view =>
      match selection? view (.suggestion id) with
      | some { expected := .retry source _, .. } =>
          .select
            { scope := view.scope
              serial := view.serial
              programVersion := view.programVersion
              id := .suggestion id
              expected := .retry source effort }
            rest
      | _ => .stop rest
  | .stale id :: rest, view =>
      match selection? view id with
      | some selection => .select { selection with serial := selection.serial + 1 } rest
      | none => .stop rest

def controller : Controller Rank (List Command) where
  key := { name := "policy-driver.script", version := 0 }
  update state _ := state
  choose := choose

abbrev Calls := List (String × Nat)

def invokeLogged (calls : Calls) (request : RuleRequest Rank) : Outcome Rank × Calls :=
  (invoke request, calls ++ [(request.action.key.name, request.action.effort)])

def run? (fuel : Nat) (commands : List Command)
    (state? : Option (State Rank) := initial?) : Option (Result Rank Calls (List Command)) := do
  let state <- state?
  some (drive controller invokeLogged fuel state [] commands)

def contradictionDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .contradiction candidate else .noChange

def contradictionInitial? : Option (State Rank) := do
  let engine <- match Engine.start contradictionDomain program #[fRule, gRule] #[0, 0]
      engineLimits with
    | .ok engine => some engine
    | .error _ => none
  some (State.start engine policyLimits)

def factResourceInitial? : Option (State Rank) := do
  let engine <- match Engine.start rightResourceDomain program #[fRule, gRule] #[0, 0]
      engineLimits with
    | .ok engine => some engine
    | .error _ => none
  some (State.start engine policyLimits)

def invokeUndeclared (calls : Calls) (request : RuleRequest Rank) :
    Outcome Rank × Calls :=
  (.success
      [{ node := node 0, fact := 1, payload := { index := request.action.serial } }]
      [] {}, calls ++ [(request.action.key.name, request.action.effort)])

def invokeFailed (calls : Calls) (request : RuleRequest Rank) :
    Outcome Rank × Calls :=
  (.failed 73, calls ++ [(request.action.key.name, request.action.effort)])

def invokeLimited (calls : Calls) (request : RuleRequest Rank) :
    Outcome Rank × Calls :=
  (.resourceLimit 59, calls ++ [(request.action.key.name, request.action.effort)])

/-! # Exact event predicates -/

def exactSelection (selection : Selection) (serial programVersion : Nat)
    (id : OfferId) : Bool :=
  selection.scope == { index := 0 } && selection.serial == serial &&
    selection.programVersion == programVersion && selection.id == id

def exactInvokeSelection (selection : Selection) (serial programVersion : Nat)
    (id : OfferId) (invocation : InvocationKey) : Bool :=
  exactSelection selection serial programVersion id &&
    selection.expected == .invoke invocation

def exactRetrySelection (selection : Selection) (serial programVersion : Nat)
    (id : SuggestionId) (source : InvocationKey) (effort : Nat) : Bool :=
  exactSelection selection serial programVersion (.suggestion id) &&
    selection.expected == .retry source effort

def exactInstanceSelection (selection : Selection) (serial programVersion : Nat)
    (id : SuggestionId) (expectedSource : InvocationKey) : Bool :=
  exactSelection selection serial programVersion (.suggestion id) &&
    match selection.expected with
    | .instantiate source request =>
        source == expectedSource &&
          request.family == 31 && request.generation == 1 &&
          request.nodes ==
            [{ domain := real
               op := { index := 2 }
               args := [.existing (node 0)] }] &&
          request.equalities ==
            [{ left := .existing (node 1), right := .proposed 0 }]
    | _ => false

def exactEqualitySelection (selection : Selection) (serial : Nat)
    (observation : EqualityObservation Rank) : Bool :=
  exactSelection selection serial 1 (.equality (equality 0)) &&
    selection.expected == .equality observation.key

def exactSplitSelection (selection : Selection) (serial programVersion : Nat)
    (plan : SplitPlan Rank) : Bool :=
  exactSelection selection serial programVersion (.suggestion (suggestion 2)) &&
    selection.expected == .split plan.source
      { node := plan.node, version := plan.version } plan.point plan.reason

def exactRetryFirstEvents (events : Array (Event Rank)) : Bool :=
  match events.toList with
  | [.rule fSelection fObservation,
      .rule retrySelection retryObservation,
      .instance instanceSelection (.admitted [fresh]),
      .equality firstEqualitySelection firstEquality,
      .rule gSelection gObservation,
      .equality lastEqualitySelection lastEquality,
      .splitPrepared splitSelection plan] =>
      exactInitialObservation fObservation &&
        exactInvokeSelection fSelection 0 0 (.application (application 0))
          fObservation.invocation &&
        exactRetryObservation retryObservation true &&
        exactRetrySelection retrySelection 1 0 (suggestion 0)
          fObservation.invocation 1 &&
        fresh == node 2 &&
        exactInstanceSelection instanceSelection 2 0 (suggestion 1)
          fObservation.invocation &&
        exactEqualityObservation firstEquality .improved
          (some (node 2, 0, 4, 0, 1)) &&
        exactEqualitySelection firstEqualitySelection 3 firstEquality &&
        exactGObservation gObservation 4 &&
        exactInvokeSelection gSelection 4 1 (.application (application 1))
          gObservation.invocation &&
        exactEqualityObservation lastEquality .noChange none &&
        exactEqualitySelection lastEqualitySelection 5 lastEquality &&
        exactSplit plan && exactSplitSelection splitSelection 6 1 plan
  | _ => false

def exactInstantiationFirstEvents (events : Array (Event Rank)) : Bool :=
  match events.toList with
  | [.rule fSelection fObservation,
      .instance instanceSelection (.admitted [fresh]),
      .rule gSelection gObservation,
      .equality firstEqualitySelection firstEquality,
      .equality lastEqualitySelection lastEquality,
      .dismissal retrySelection false true,
      .splitPrepared splitSelection plan] =>
      exactInitialObservation fObservation &&
        exactInvokeSelection fSelection 0 0 (.application (application 0))
          fObservation.invocation &&
        fresh == node 2 &&
        exactInstanceSelection instanceSelection 1 0 (suggestion 1)
          fObservation.invocation &&
        exactGObservation gObservation 0 &&
        exactInvokeSelection gSelection 2 1 (.application (application 1))
          gObservation.invocation &&
        exactEqualityObservation firstEquality .improved
          (some (node 1, 1, 4, 1, 2)) &&
        exactEqualitySelection firstEqualitySelection 3 firstEquality &&
        exactEqualityObservation lastEquality .noChange none &&
        exactEqualitySelection lastEqualitySelection 4 lastEquality &&
        exactRetrySelection retrySelection 5 1 (suggestion 0)
          fObservation.invocation 1 &&
        exactSplit plan && exactSplitSelection splitSelection 6 1 plan
  | _ => false

def retryFirstCommands : List Command :=
  [.select (.application (application 0)),
    .select (.suggestion (suggestion 0)),
    .select (.suggestion (suggestion 1)),
    .select (.equality (equality 0)),
    .select (.application (application 1)),
    .select (.equality (equality 0)),
    .select (.suggestion (suggestion 2))]

def instantiationFirstCommands : List Command :=
  [.select (.application (application 0)),
    .select (.suggestion (suggestion 1)),
    .select (.application (application 1)),
    .select (.equality (equality 0)),
    .select (.equality (equality 0)),
    .dismiss (.suggestion (suggestion 0)),
    .select (.suggestion (suggestion 2))]

/-! # Two valid schedules, one semantic result -/

#guard
  match run? 7 retryFirstCommands with
  | some result =>
      result.policy == controller.key &&
        exactRetryFirstEvents result.events && result.state.engine.facts.toList == [0, 4, 4] &&
        result.cache == [(fKey.name, 0), (fKey.name, 1), (gKey.name, 0)] &&
        result.policyState.isEmpty && result.state.metrics.decisions == 7 &&
        match result.stop with
        | .split plan => exactSplit plan
        | _ => false
  | none => false

#guard
  match run? 7 instantiationFirstCommands with
  | some result =>
      exactInstantiationFirstEvents result.events &&
        result.state.engine.facts.toList == [0, 4, 4] &&
        result.cache == [(fKey.name, 0), (gKey.name, 0)] &&
        result.policyState.isEmpty && result.state.metrics.decisions == 7 &&
        match result.stop with
        | .split plan => exactSplit plan
        | _ => false
  | none => false

/-! # Saturation and stopping boundaries -/

def saturationCommands : List Command :=
  retryFirstCommands.dropLast ++ [.dismiss (.suggestion (suggestion 2))]

def declineNarrowingCommands : List Command :=
  [.dismiss (.suggestion (suggestion 0)),
    .dismiss (.suggestion (suggestion 1)),
    .dismiss (.suggestion (suggestion 2))]

def exactSaturationPrefix (events : Array (Event Rank)) : Bool :=
  match events.toList with
  | [.rule _ initial, .rule _ retry, .instance _ (.admitted [fresh]),
      .equality _ firstEquality, .rule _ gObservation, .equality _ lastEquality,
      .dismissal splitSelection false false, .saturated] =>
      exactInitialObservation initial && exactRetryObservation retry true &&
        fresh == node 2 &&
        exactEqualityObservation firstEquality .improved (some (node 2, 0, 4, 0, 1)) &&
        exactGObservation gObservation 4 &&
        exactEqualityObservation lastEquality .noChange none &&
        exactSelection splitSelection 6 1 (.suggestion (suggestion 2))
  | _ => false

-- The final permitted transition may expose a genuine fixed point.  The
-- zero-fuel boundary must inspect that state and report saturation.
#guard
  match run? 7 saturationCommands with
  | some result =>
      exactSaturationPrefix result.events && result.policyState.isEmpty &&
        result.state.metrics.decisions == 7 &&
        match result.stop with
        | .saturated => true
        | _ => false
  | none => false

-- With one fewer transition, live split work remains and the same run reports
-- fuel exhaustion rather than a false fixed point.
#guard
  match run? 6 saturationCommands with
  | some result =>
      result.events.size == 7 &&
        match result.events.back?, result.stop with
        | some .driverFuel, .driverFuel => true
        | _, _ => false
  | none => false

-- A split is optional, but retries and instantiations can still improve the
-- current scope. Declining all three empties the frontier without proving a
-- propagation fixed point.
#guard
  match run? 3 declineNarrowingCommands afterInitial? with
  | some result =>
      result.state.incomplete && result.policyState.isEmpty &&
        result.state.metrics.decisions == 4 &&
        match result.events.toList, result.stop with
        | [.dismissal retry false true, .dismissal instanceSelection false true,
            .dismissal split false false, .incomplete],
            .unknown .incomplete =>
              exactSelection retry 1 0 (.suggestion (suggestion 0)) &&
                exactSelection instanceSelection 2 0 (.suggestion (suggestion 1)) &&
                exactSelection split 3 0 (.suggestion (suggestion 2))
        | _, _ => false
  | none => false

-- Contradiction reached on the final permitted transition is the answer, not
-- driver-fuel exhaustion.
#guard
  match run? 1 [.select (.application (application 0))] contradictionInitial? with
  | some result =>
      result.state.engine.contradictory && result.state.engine.facts.toList == [0, 1] &&
        match result.events.toList, result.stop with
        | [.rule selection observation, .contradiction], .contradiction =>
            exactInvokeSelection selection 0 0 (.application (application 0))
                observation.invocation &&
              observation.outcome == .success && observation.contradiction &&
              oneChange observation.changes (node 1) 0 1 0 1
        | _, _ => false
  | none => false

-- An arbitrary registry cannot write outside the selected registration. The
-- rejection retains the exact invocation identity derived by the engine.
#guard
  match initial? with
  | none => false
  | some state =>
      let result := drive controller invokeUndeclared 1 state []
        [.select (.application (application 0))]
      let resumed := drive controller invokeLogged 0 result.state result.cache []
      result.cache == [(fKey.name, 0)] && result.state.incomplete &&
        result.state.engine.pending.isNone &&
        (match result.events.toList, result.stop with
          | [.replyRejected selection invocation (.undeclaredWrite target)],
              .invalidReply (.undeclaredWrite stoppedTarget) =>
                target == node 0 && stoppedTarget == node 0 &&
                  exactInvokeSelection selection 0 0 (.application (application 0))
                    invocation
          | _, _ => false) &&
        match resumed.events.toList, resumed.stop with
        | [.incomplete], .unknown .incomplete => resumed.state.incomplete
        | _, _ => false

-- A registry failure is an accepted, typed observation, but it cannot close
-- the selected propagation obligation.  An empty frontier is therefore
-- unknown rather than saturated.
#guard
  match initial? with
  | none => false
  | some state =>
      let result := drive controller invokeFailed 1 state []
        [.select (.application (application 0))]
      result.state.incomplete && result.state.engine.pending.isNone &&
        result.cache == [(fKey.name, 0)] &&
        match result.events.toList, result.stop with
        | [.rule selection observation, .incomplete], .unknown .incomplete =>
            exactInvokeSelection selection 0 0 (.application (application 0))
                observation.invocation &&
              observation.outcome == .failed 73 && observation.changes.isEmpty
        | _, _ => false

-- A rule-declared resource limit has the same completeness boundary.  It is
-- not an engine resource stop and cannot be reinterpreted as inapplicability.
#guard
  match initial? with
  | none => false
  | some state =>
      let result := drive controller invokeLimited 1 state []
        [.select (.application (application 0))]
      result.state.incomplete && result.state.engine.pending.isNone &&
        result.cache == [(fKey.name, 0)] &&
        match result.events.toList, result.stop with
        | [.rule selection observation, .incomplete], .unknown .incomplete =>
            exactInvokeSelection selection 0 0 (.application (application 0))
                observation.invocation &&
              observation.outcome == .resourceLimit 59 && observation.changes.isEmpty
        | _, _ => false

#guard
  match run? 1 [.stop] with
  | some result =>
      result.state.metrics.decisions == 0 &&
        match result.events.toList, result.stop with
        | [.policyStop 1], .unknown (.policyStop 1) => true
        | _, _ => false
  | none => false

#guard
  match run? 1 [.dismiss (.application (application 0))] with
  | some result =>
      result.state.metrics.decisions == 1 &&
        match result.events.toList, result.stop with
        | [.dismissal selection true true], .unknown (.requiredDismissal stopped) =>
            exactSelection selection 0 0 (.application (application 0)) &&
              selection.serial == stopped.serial && selection.id == stopped.id
        | _, _ => false
  | none => false

/-! # Resource boundaries -/

def initialWithLimits? (limits : Experiment.Propagator.Policy.Limits) : Option (State Rank) :=
  initialWith? limits

-- An engine resource stop rolls back the candidate transaction but consumes
-- the selected application. Restarting from the returned snapshot therefore
-- reports incomplete rather than saturation.
#guard
  match PolicyConformance.initialWithLimits?
      { engineLimits with maxAcceptedFacts := 0 } policyLimits with
  | none => false
  | some state =>
      let result := drive controller invokeLogged 1 state []
        [.select (.application (application 0))]
      let resumed := drive controller invokeLogged 0 result.state result.cache []
      result.state.incomplete && result.state.engine.pending.isNone &&
        (match result.events.toList, result.stop with
          | [.engineResource (.invocation selection invocation) .acceptedFacts],
              .engineResource .acceptedFacts =>
                exactInvokeSelection selection 0 0 (.application (application 0))
                  invocation
          | _, _ => false) &&
        match resumed.events.toList, resumed.stop with
        | [.incomplete], .unknown .incomplete => resumed.state.incomplete
        | _, _ => false

-- Fact-domain resource exhaustion carries its exact budget and the same
-- completeness status.
#guard
  match factResourceInitial? with
  | none => false
  | some state =>
      let result := drive controller invokeLogged 1 state []
        [.select (.application (application 0))]
      result.state.incomplete && result.state.engine.pending.isNone &&
        match result.events.toList, result.stop with
        | [.factResource (.invocation selection invocation) 77], .factResource 77 =>
            exactInvokeSelection selection 0 0 (.application (application 0))
              invocation
        | _, _ => false

#guard
  match run? 2 retryFirstCommands
      (initialWithLimits? { policyLimits with maxDecisions := 1 }) with
  | some result =>
      result.state.metrics.decisions == 1 &&
        match result.events.toList, result.stop with
        | [.rule selection observation, .decisionResource], .decisionResource =>
            exactInitialObservation observation &&
              exactSelection selection 0 0 (.application (application 0))
        | _, _ => false
  | none => false

#guard
  match run? 2 retryFirstCommands
      (initialWithLimits? { policyLimits with maxTraversal := 2 }) with
  | some result =>
      result.state.metrics.decisions == 1 && result.state.metrics.traversal == 2 &&
        match result.events.toList, result.stop with
        | [.rule selection observation, .viewResource .traversalLimit],
            .viewResource .traversalLimit =>
            exactInitialObservation observation &&
              exactSelection selection 0 0 (.application (application 0))
        | _, _ => false
  | none => false

/-! # Typed equality stops -/

-- Equality resource failures remain typed observations, then stop the driver
-- with a second event which identifies the selected policy choice as origin.
#guard
  match run? 1 [.select (.equality (equality 0))]
      (equalityReadyWith? { engineLimits with maxAcceptedFacts := 1 } rankDomain) with
  | some result =>
      result.cache.isEmpty && result.state.metrics.decisions == 2 &&
        result.state.engine.equalityQueued[0]? == some true &&
        match result.events.toList, result.stop with
        | [.equality selection observation,
            .engineResource (.choice origin) .acceptedFacts],
            .engineResource .acceptedFacts =>
              exactEqualitySelection selection 1 observation &&
                exactEqualitySelection origin 1 observation &&
                observation.outcome == .engineResource .acceptedFacts &&
                observation.narrowCalls == 2 && observation.changes.isEmpty
        | _, _ => false
  | none => false

#guard
  match run? 1 [.select (.equality (equality 0))]
      (equalityReadyWith? engineLimits rightResourceDomain) with
  | some result =>
      result.cache.isEmpty && result.state.metrics.decisions == 2 &&
        result.state.engine.equalityQueued[0]? == some true &&
        match result.events.toList, result.stop with
        | [.equality selection observation, .factResource (.choice origin) 77],
            .factResource 77 =>
              exactEqualitySelection selection 1 observation &&
                exactEqualitySelection origin 1 observation &&
                observation.outcome == .factResource 77 &&
                observation.narrowCalls == 2 && observation.changes.isEmpty
        | _, _ => false
  | none => false

-- A domain fault carries its exact typed cause and actual call count in the
-- equality event before the driver reports that the engine state is invalid.
#guard
  match run? 1 [.select (.equality (equality 0))]
      (equalityReadyWith? engineLimits leftMalformedDomain) with
  | some result =>
      result.cache.isEmpty && result.state.metrics.decisions == 2 &&
        result.state.engine.equalityQueued[0]? == some true &&
        match result.events.toList, result.stop with
        | [.equality selection observation, .invalidState], .invalidState =>
            exactEqualitySelection selection 1 observation &&
              observation.outcome == .invalid (.malformedFact 91) &&
              observation.narrowCalls == 1 && observation.changes.isEmpty
        | _, _ => false
  | none => false

/-! # Revalidation of untrusted selections -/

#guard
  match run? 2 [.stale (.application (application 0)), .stop] with
  | some result =>
      result.state.metrics.decisions == 1 && result.state.metrics.rejected == 1 &&
        match result.events.toList, result.stop with
        | [.choiceRejected selection .staleSerial, .policyStop 1],
            .unknown (.policyStop 1) =>
            selection.serial == 1 && selection.id == .application (application 0)
        | _, _ => false
  | none => false

#guard
  match run? 2 [.wrongRetry (suggestion 0) 2, .stop] afterInitial? with
  | some result =>
      result.state.metrics.decisions == 2 && result.state.metrics.rejected == 1 &&
        match result.events.toList, result.stop with
        | [.choiceRejected selection .wrongKey, .policyStop 3],
            .unknown (.policyStop 3) =>
            match selection.expected with
            | .retry source 2 => source.rule == fKey && source.effort == 0
            | _ => false
        | _, _ => false
  | none => false

/-! # Split plans are returned, never executed by the driver -/

#guard
  match run? 1 [.select (.suggestion (suggestion 2))] afterInitial? with
  | some result =>
      result.cache.isEmpty && result.state.metrics.decisions == 2 &&
        match result.events.toList, result.stop with
        | [.splitPrepared selection plan], .split stopped =>
            exactSplitSelection selection 1 0 plan &&
              exactSplit plan && exactSplit stopped
        | _, _ => false
  | none => false

end Hex.Interval.PolicyDriverConformance
