/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.TargetRun

@[expose] public section

/-!
# A replaceable staged interval-search policy

This first policy candidate is deliberately representation- and
function-independent. It ranks only engine-owned offer classes, action kinds,
ages, and bounded effort. Package keys and facts remain opaque.

The policy is an experiment, not a soundness boundary. Every selection is
still validated by `PolicySession`, and proof replay remains independent of
the order chosen here.
-/

namespace Hex.Interval.Experiment.StagedPolicy

open Propagator Propagator.Policy TargetRun

local notation "PolicyOffer" =>
  Hex.Interval.Policy.OfferView Propagator.Policy.OfferId Propagator.Policy.OfferKey

/-- Replaceable feature gates for the staged baseline. -/
structure Config where
  allowInstantiation : Bool := true
  allowRetries : Bool := true
  allowSplits : Bool := true
  maxRetryEffort : Nat := 4
  deriving DecidableEq, Repr

/-- Policy-private observations. These counters affect diagnostics and future
policy upgrades, never the validity of an installed fact. -/
structure Metrics where
  ruleRuns : Nat := 0
  equalityRuns : Nat := 0
  improvements : Nat := 0
  noChanges : Nat := 0
  inapplicable : Nat := 0
  failures : Nat := 0
  extensions : Nat := 0
  dismissals : Nat := 0
  rejections : Nat := 0
  deriving DecidableEq, Repr

structure State where
  config : Config
  metrics : Metrics := {}
  deriving DecidableEq, Repr

def State.initial (config : Config := {}) : State := { config }

def splitReasonRank : SplitReason -> Nat
  | .singularity => 0
  | .totalityBoundary => 1
  | .kink => 2
  | .criticalPoint => 3
  | .contractor => 4
  | .smallLandmark => 5
  | .midpoint => 6
  | .custom code => 7 + code

/-- Coarse replaceable stages. Lower values run first. An invocation which
discovers an instantiation or split precedes the resulting semantic offer. -/
def rank : PolicyOffer -> Nat
  | { key := .equality _, .. } => 0
  | { key := .invoke invocation, .. } =>
      match invocation.kind with
      | .forward | .backward | .rewrite => 0
      | .instantiate => 10
      | .improve | .shave | .regularize => 20
      | .split => 30
  | { key := .instantiate _ _, .. } => 11
  | { key := .retry _ _, .. } => 21
  | { key := .split _ _ _ reason, .. } => 40 + splitReasonRank reason

def allowed (config : Config) (offer : PolicyOffer) : Bool :=
  match offer.key with
  | .retry _ effort => config.allowRetries && effort <= config.maxRetryEffort
  | .instantiate _ _ => config.allowInstantiation
  | .split _ _ _ _ => config.allowSplits
  | .invoke invocation =>
      match invocation.kind with
      | .instantiate => config.allowInstantiation
      | .split => config.allowSplits
      | .forward | .backward | .improve | .shave | .rewrite | .regularize => true
  | .equality _ => true

def better (candidate current : PolicyOffer) : Bool :=
  rank candidate < rank current ||
    (rank candidate == rank current && current.age < candidate.age)

/-- Select the oldest offer in the earliest enabled stage. Array order is the
final deterministic tie-breaker. -/
def choose? (config : Config) (offers : Array PolicyOffer) : Option PolicyOffer :=
  offers.foldl (fun best candidate =>
    if !allowed config candidate then best
    else
      match best with
      | none => some candidate
      | some current => if better candidate current then some candidate else best) none

def recordRule (metrics : Metrics) (observation : RuleObservation Fact) : Metrics :=
  let improved := observation.changes.size
  { metrics with
    ruleRuns := metrics.ruleRuns + 1
    improvements := metrics.improvements + improved
    noChanges := metrics.noChanges + if observation.outcome == .noChange then 1 else 0
    inapplicable := metrics.inapplicable +
      if observation.outcome == .inapplicable then 1 else 0
    failures := metrics.failures +
      if observation.outcome matches .failed _ | .resourceLimit _ then 1 else 0 }

def recordEquality (metrics : Metrics)
    (observation : EqualityObservation Fact) : Metrics :=
  { metrics with
    equalityRuns := metrics.equalityRuns + 1
    improvements := metrics.improvements + observation.changes.size
    noChanges := metrics.noChanges +
      if observation.outcome == .noChange then 1 else 0
    failures := metrics.failures +
      if observation.outcome matches .engineResource _ | .factResource _ | .invalid _
      then 1 else 0 }

def update : State -> Event Fact -> State
  | state, .rule observation =>
      { state with metrics := recordRule state.metrics observation }
  | state, .equality observation =>
      { state with metrics := recordEquality state.metrics observation }
  | state, .instance completion =>
      match completion with
      | .instanceAdmitted _ =>
          { state with
            metrics := { state.metrics with extensions := state.metrics.extensions + 1 } }
      | .instanceDuplicate | .instanceRejected _ => state
      | .dismissed =>
          { state with
            metrics := { state.metrics with dismissals := state.metrics.dismissals + 1 } }
  | state, .dismissed =>
      { state with
        metrics := { state.metrics with dismissals := state.metrics.dismissals + 1 } }
  | state, .rejected _ =>
      { state with
        metrics := { state.metrics with rejections := state.metrics.rejections + 1 } }
  | state, .invalidPayload _ | state, .rejectedPayload _ =>
      { state with
        metrics := { state.metrics with failures := state.metrics.failures + 1 } }

/-- Generic target-run controller for the staged baseline. -/
def controller : TargetRun.Controller Fact State where
  update := update
  choose := fun state view =>
    match choose? state.config view.offers with
    | some offer => .select offer state
    | none => .stop state

end Hex.Interval.Experiment.StagedPolicy
