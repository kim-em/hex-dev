/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.StagedPolicy
import HexInterval.Experiment.ExpSign
import HexInterval.Experiment.SemanticReplay

/-!
# Staged policy conformance

The controller below knows no rule keys. On a live arbitrary-function graph it
drains two forward contractors before invoking a split probe and selecting the
resulting solver split.
-/

namespace Hex.Interval.StagedPolicyConformance

open Experiment
open Propagator PolicySession SemanticReplay TargetRun
open ExpSign StagedPolicy

private def program : Program :=
  { operations
    nodes := #[sourceInstruction, expInstruction, expInstruction] }

private def input : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := #[.all, .all, .all]
    target := { node := node 2, fact := .empty } }

private def session? : Option (PolicySession.Session Bound) :=
  match PolicySession.Session.start factDomain program splitPackages
      input.initialFacts limits { index := 0 } with
  | .ok session => some session
  | .error _ => none

private def result? : Option (TargetRun.Result Bound StagedPolicy.State) := do
  let session ← session?
  pure (TargetRun.drive factDomain input.target.node input.target.fact
    StagedPolicy.controller 16 session StagedPolicy.State.initial)

private def expectedMetrics : StagedPolicy.Metrics :=
  { ruleRuns := 3, improvements := 2 }

/- Cheap forward work reaches a fixed point before the split probe and its
resulting semantic split offer. -/
#guard
  result?.any fun result =>
    result.events.size == 3 &&
      result.session.state.engine.history.size == 2 &&
      result.session.state.engine.facts == #[.all, .nonnegative, .nonnegative] &&
      result.policyState.metrics == expectedMetrics &&
      match result.events[0]?, result.events[1]?, result.events[2]?, result.stop with
      | some (TargetRun.Event.rule first), some (TargetRun.Event.rule second),
          some (TargetRun.Event.rule probe), TargetRun.Stop.split plan =>
          first.invocation.kind == .forward && first.invocation.anchor == node 1 &&
            first.changes.size == 1 &&
            second.invocation.kind == .forward && second.invocation.anchor == node 2 &&
            second.changes.size == 1 &&
            probe.invocation.kind == .split && probe.invocation.anchor == node 0 &&
            probe.changes.isEmpty && probe.emittedSuggestions.size == 1 &&
            plan.node == node 0 && plan.point == 0 && plan.reason == .smallLandmark
      | _, _, _, _ => false

private def invocation (index : Nat) (kind : ActionKind) : Policy.InvocationKey :=
  { scope := { index := 0 }
    programVersion := 0
    application := { index }
    rule := { name := "staged-policy.synthetic" }
    anchor := node index
    kind
    effort := 0
    inputs := [] }

private def offer (index age : Nat) (key : Policy.OfferKey) : Policy.OfferView :=
  { id := .suggestion { index }, key, offerClass := key.offerClass, age }

private def forwardOffer : Policy.OfferView :=
  offer 0 1 (.invoke (invocation 0 .forward))

private def olderForward : Policy.OfferView :=
  offer 1 5 (.invoke (invocation 1 .forward))

private def instanceOffer : Policy.OfferView :=
  offer 2 9 (.invoke (invocation 2 .instantiate))

private def retryOffer : Policy.OfferView :=
  offer 3 9 (.retry (invocation 3 .improve) 2)

private def splitOffer : Policy.OfferView :=
  offer 4 9 (.split (invocation 4 .split)
    { node := node 0, version := 0 } 0 .midpoint)

#guard
  (StagedPolicy.choose? {} #[splitOffer, retryOffer, instanceOffer, forwardOffer]).map
      (fun selected => selected.key) == some forwardOffer.key

#guard
  (StagedPolicy.choose? {} #[forwardOffer, olderForward]).map
      (fun selected => selected.key) == some olderForward.key

#guard
  (StagedPolicy.choose?
      { allowInstantiation := false, allowRetries := false, allowSplits := false }
      #[splitOffer, retryOffer, instanceOffer]).isNone

end Hex.Interval.StagedPolicyConformance
