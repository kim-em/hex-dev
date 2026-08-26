/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.StagedPolicy
import HexInterval.Experiment.ExpSign
import HexInterval.Experiment.SemanticReplay
import HexInterval.Experiment.AdaptivePolicy

/-!
# Staged policy conformance

The controller below knows no rule keys. On a live arbitrary-function graph it
drains two forward contractors before invoking a split probe and selecting the
resulting solver split.
-/

namespace Hex.Interval.StagedPolicyConformance

local notation "OfferView" =>
  Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "Selection" =>
  Hex.Interval.Policy.Decision _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "ScopeId" => Hex.Interval.Policy.ScopeId
local notation "OfferClass" => Hex.Interval.Policy.OfferClass

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

private def disabledResult? : Option (TargetRun.Result Bound StagedPolicy.State) := do
  let session ← session?
  pure (TargetRun.drive factDomain input.target.node input.target.fact
    StagedPolicy.controller 16 session
      (StagedPolicy.State.initial
        { allowInstantiation := false
          allowRetries := false
          allowSplits := false }))

-- Enabled semantic work still passes through the ordinary session boundary.
-- Once only the disabled split-discovery offer remains, the controller stops
-- honestly with that live offer retained rather than selecting it.
#guard
  disabledResult?.any fun result =>
    result.events.size == 2 &&
      result.session.state.engine.history.size == 2 &&
      result.session.state.engine.facts == #[.all, .nonnegative, .nonnegative] &&
      match result.stop with
      | .policyStop liveOffers => liveOffers == 1
      | _ => false

private def invocation (index : Nat) (kind : ActionKind) : Policy.InvocationKey :=
  { scope := { index := 0 }
    programVersion := 0
    application := { index }
    rule := { name := "staged-policy.synthetic" }
    anchor := node index
    kind
    effort := 0
    inputs := [] }

private def offer (index age : Nat) (key : Policy.OfferKey) : OfferView :=
  { id := .suggestion { index }, key, offerClass := key.offerClass, age }

private def forwardOffer : OfferView :=
  offer 0 1 (.invoke (invocation 0 .forward))

private def olderForward : OfferView :=
  offer 1 5 (.invoke (invocation 1 .forward))

private def instanceProbe : OfferView :=
  offer 2 9 (.invoke (invocation 2 .instantiate))

private def instanceOffer : OfferView :=
  offer 3 9 (.instantiate (invocation 3 .instantiate)
    { family := 0, generation := 0, nodes := [], equalities := [], scopes := [] })

private def retryOffer : OfferView :=
  offer 4 9 (.retry (invocation 4 .improve) 2)

private def splitProbe : OfferView :=
  offer 5 9 (.invoke (invocation 5 .split))

private def splitOffer : OfferView :=
  offer 6 9 (.split (invocation 6 .split)
    { node := node 0, version := 0 } 0 .midpoint)

#guard
  (StagedPolicy.choose? {}
      #[splitOffer, retryOffer, instanceOffer, instanceProbe, forwardOffer]).map
      (fun selected => selected.key) == some forwardOffer.key

#guard
  (StagedPolicy.choose? {} #[forwardOffer, olderForward]).map
      (fun selected => selected.key) == some olderForward.key

#guard
  (StagedPolicy.choose? { allowInstantiation := false }
      #[instanceProbe, instanceOffer]).isNone

#guard
  (StagedPolicy.choose? { allowRetries := false } #[retryOffer]).isNone

#guard
  (StagedPolicy.choose? { maxRetryEffort := 1 } #[retryOffer]).isNone

#guard
  (StagedPolicy.choose? { allowSplits := false }
      #[splitProbe, splitOffer]).isNone

/-! ## Feedback-guided policy -/

namespace Adaptive

open AdaptivePolicy

private def invocation (index effort : Nat) (kind : ActionKind := .forward) :
    Policy.InvocationKey :=
  { scope := { index := 0 }
    programVersion := 0
    application := { index }
    rule := { name := "adaptive-policy.synthetic" }
    anchor := node index
    kind
    effort
    inputs := [] }

private def offer (index age : Nat) (key : Policy.OfferKey) : OfferView :=
  { id := .application { index }, key, offerClass := key.offerClass, age }

private def change (index : Nat) : Policy.FactDelta Nat :=
  { node := node index
    before := 0
    after := 1
    beforeVersion := 0
    afterVersion := 1 }

private def observation (key : Policy.InvocationKey)
    (outcome : Policy.OutcomeTag) (changes : Array (Policy.FactDelta Nat))
    (cost : CostObservation := {}) : Policy.RuleObservation Nat :=
  { invocation := key
    outcome
    changes
    contradiction := false
    cost
    suggestionPlan := {}
    emittedSuggestions := #[] }

private def config : AdaptivePolicy.Config :=
  { optimism := 16
    gainWeight := 96
    noChangePenalty := 12
    ageBonusCap := 4
    fairnessAge := 20 }

private def productiveKey := invocation 0 0
private def quietKey := invocation 1 0
private def freshKey := invocation 2 0

private def learned : AdaptivePolicy.State :=
  let initial := AdaptivePolicy.State.initial config
  let afterProductive := AdaptivePolicy.update initial <|
    .rule (observation productiveKey .success #[change 0]
      { arithmeticWork := 1 })
  AdaptivePolicy.update afterProductive <|
    .rule (observation quietKey .noChange #[] { arithmeticWork := 1 })

private def productiveOffer := offer 0 1 (.invoke productiveKey)
private def quietOffer := offer 1 4 (.invoke quietKey)
private def freshOffer := offer 2 0 (.invoke freshKey)

/- Actual gain beats a somewhat older fixed-point action. -/
#guard
  (AdaptivePolicy.choose? learned #[quietOffer, productiveOffer]).map
      (fun selected => selected.key) == some productiveOffer.key

/- An untried action receives optimism rather than inheriting a sibling's
fixed-point history. -/
#guard
  (AdaptivePolicy.choose? learned #[quietOffer, freshOffer]).map
      (fun selected => selected.key) == some freshOffer.key

/- The shipped coefficients reward one unit-cost improvement over an untried
peer.  This guard deliberately constructs `Config := {}` so later fixture
tuning cannot silently replace coverage of the public defaults. -/
private def defaultLearned : AdaptivePolicy.State :=
  AdaptivePolicy.update (AdaptivePolicy.State.initial {}) <|
    .rule (observation productiveKey .success #[change 0]
      { arithmeticWork := 1 })

#guard
  (AdaptivePolicy.choose? defaultLearned #[freshOffer, { productiveOffer with age := 0 }]).map
      (fun selected => selected.key) == some productiveOffer.key

/- A repeated fixed point on one exact snapshot decays below an untried peer. -/
private def defaultStagnant : AdaptivePolicy.State :=
  AdaptivePolicy.update defaultLearned <|
    .rule (observation productiveKey .noChange #[] { arithmeticWork := 1 })

#guard
  (AdaptivePolicy.choose? defaultStagnant
      #[{ productiveOffer with age := 0 }, freshOffer]).map
      (fun selected => selected.key) == some freshOffer.key

/- A changed input version keeps stable-site gain history but resets the
exact-snapshot fixed-point penalty. -/
private def rewokenProductiveKey : Policy.InvocationKey :=
  { productiveKey with inputs := [{ node := node 0, version := 1 }] }

private def rewokenProductiveOffer : OfferView :=
  offer 0 0 (.invoke rewokenProductiveKey)

#guard
  (AdaptivePolicy.choose? defaultStagnant #[freshOffer, rewokenProductiveOffer]).map
      (fun selected => selected.key) == some rewokenProductiveOffer.key

/- A changed snapshot with no accumulated gain receives the optimism floor;
without the `Nat.max` branch this score would be zero. -/
private def noGain : AdaptivePolicy.State :=
  AdaptivePolicy.update (AdaptivePolicy.State.initial {}) <|
    .rule (observation productiveKey .noChange #[] { arithmeticWork := 1 })

#guard
  (AdaptivePolicy.find? noGain.records
      (AdaptivePolicy.ruleKey rewokenProductiveKey)).isSome &&
    (AdaptivePolicy.rankOffer noGain rewokenProductiveOffer).score ==
      ({} : AdaptivePolicy.Config).optimism

private def accumulated : AdaptivePolicy.State :=
  AdaptivePolicy.update defaultStagnant <|
    .rule (observation rewokenProductiveKey .success #[change 0]
      { arithmeticWork := 1 })

#guard
  accumulated.records.length == 1 &&
    (AdaptivePolicy.find? accumulated.records
      (AdaptivePolicy.ruleKey rewokenProductiveKey)).any fun record =>
        record.runs == 3 && record.improvements == 2 &&
          record.noChanges == 1 && record.stagnant == 0

/- The feedback table has an explicit deterministic capacity. -/
private def bounded : AdaptivePolicy.State :=
  let state := AdaptivePolicy.State.initial { maxRecords := 2 }
  let state := AdaptivePolicy.update state <|
    .rule (observation productiveKey .success #[change 0])
  let state := AdaptivePolicy.update state <|
    .rule (observation quietKey .success #[change 1])
  AdaptivePolicy.update state <|
    .rule (observation freshKey .success #[change 2])

#guard
  bounded.records.length == 2 &&
    (AdaptivePolicy.find? bounded.records
      (AdaptivePolicy.ruleKey productiveKey)).isNone

/- Updating an existing site moves it to the MRU front, so the next insertion
evicts the other retained site deterministically. -/
private def touchedBounded : AdaptivePolicy.State :=
  let state := AdaptivePolicy.State.initial { maxRecords := 2 }
  let state := AdaptivePolicy.update state <|
    .rule (observation productiveKey .success #[change 0])
  let state := AdaptivePolicy.update state <|
    .rule (observation quietKey .success #[change 1])
  let state := AdaptivePolicy.update state <|
    .rule (observation productiveKey .noChange #[])
  AdaptivePolicy.update state <|
    .rule (observation freshKey .success #[change 2])

#guard
  touchedBounded.records.length == 2 &&
    (AdaptivePolicy.find? touchedBounded.records
      (AdaptivePolicy.ruleKey productiveKey)).any (fun record => record.runs == 2) &&
    (AdaptivePolicy.find? touchedBounded.records
      (AdaptivePolicy.ruleKey quietKey)).isNone &&
    (AdaptivePolicy.find? touchedBounded.records
      (AdaptivePolicy.ruleKey freshKey)).isSome

/- Stable input order is the final tie-breaker for otherwise equal offers. -/
private def tiedKey := invocation 4 0
private def tiedOffer := offer 4 0 (.invoke tiedKey)
private def unlearned := AdaptivePolicy.State.initial config

#guard
  (AdaptivePolicy.choose? unlearned #[freshOffer, tiedOffer]).map
      (fun selected => selected.key) == some freshOffer.key &&
    (AdaptivePolicy.choose? unlearned #[tiedOffer, freshOffer]).map
      (fun selected => selected.key) == some tiedOffer.key

/- Fairness is a separate tier and eventually samples an old eligible action
even when its learned score is poor. -/
private def fairQuiet := { quietOffer with age := 20 }

#guard
  (AdaptivePolicy.choose? learned #[productiveOffer, fairQuiet]).map
      (fun selected => selected.key) == some fairQuiet.key

/- Learning never lets a speculative split leapfrog unsaturated cheap
propagation merely because it is untried. -/
private def splitOffer : OfferView :=
  offer 3 0 (.split (invocation 3 0 .split)
    { node := node 0, version := 0 } 0 .midpoint)

#guard
  (AdaptivePolicy.choose? learned #[splitOffer, quietOffer]).map
      (fun selected => selected.key) == some quietOffer.key

/- Equality contractions use the same authenticated feedback channel. -/
private def equalityKey : Policy.EqualityWorkKey :=
  { scope := { index := 0 }
    programVersion := 0
    equality := { index := 0 }
    left := { node := node 0, version := 0 }
    right := { node := node 1, version := 0 } }

private def equalityLearned : AdaptivePolicy.State :=
  AdaptivePolicy.update (AdaptivePolicy.State.initial config) <|
    .equality
      { key := equalityKey
        outcome := .improved
        changes := #[change 0]
        narrowCalls := 2 }

private def equalityOffer : OfferView :=
  { id := .equality { index := 0 }
    key := .equality equalityKey
    offerClass := .equality
    age := 0 }

#guard
  (AdaptivePolicy.choose? equalityLearned #[freshOffer, equalityOffer]).map
      (fun selected => selected.key) == some equalityOffer.key

private def live? : Option (TargetRun.Result Bound AdaptivePolicy.State) := do
  let session <- session?
  pure <| TargetRun.drive factDomain input.target.node input.target.fact
    AdaptivePolicy.controller 16 session (AdaptivePolicy.State.initial config)

private def totalRuns (state : AdaptivePolicy.State) : Nat :=
  state.records.foldl (fun total record => total + record.runs) 0

private def totalImprovements (state : AdaptivePolicy.State) : Nat :=
  state.records.foldl (fun total record => total + record.improvements) 0

/- The live arbitrary-function graph supplies three independent observations;
the generic feedback table records two actual fact improvements. -/
#guard
  live?.any fun result =>
    result.events.size == 3 && result.session.state.engine.history.size == 2 &&
      result.policyState.records.length == 3 &&
      totalRuns result.policyState == 3 &&
      totalImprovements result.policyState == 2 &&
      match result.stop with
      | .split plan => plan.node == node 0 && plan.reason == .smallLandmark
      | _ => false

end Adaptive

end Hex.Interval.StagedPolicyConformance
