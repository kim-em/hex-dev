/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.StagedPolicy

@[expose] public section

/-!
# A feedback-guided interval-search policy

This policy refines `StagedPolicy` without inspecting facts, operation names,
or package keys.  It learns only from engine-authenticated observations: actual
fact-version changes and deterministic logical work.  Untried actions receive
an optimism bonus, repeated fixed points decay, and a bounded age tier prevents
continuous eligible work from starving.

The scores choose search order only.  Every selected offer is revalidated by
`PolicySession`, and proof replay is independent of this module.
-/

namespace Hex.Interval.Experiment.AdaptivePolicy

open Propagator Propagator.Policy TargetRun

/-- Replaceable integer coefficients for the first feedback experiment. -/
structure Config where
  staged : StagedPolicy.Config := {}
  optimism : Nat := 32
  gainWeight : Nat := 64
  noChangePenalty : Nat := 8
  ageBonusCap : Nat := 16
  fairnessAge : Nat := 32
  deriving DecidableEq, Repr

/-- Package-opaque identity at which feedback is accumulated.  Input versions
remain part of `invocation`, so a newly woken action is sampled afresh. -/
inductive Key where
  | invocation (invocation : InvocationKey)
  | equality (equality : EqualityWorkKey)
  deriving DecidableEq

/-- Exact, bounded observations accumulated for one selectable transition. -/
structure Record where
  key : Key
  runs : Nat := 0
  improvements : Nat := 0
  noChanges : Nat := 0
  work : Nat := 0

structure State where
  config : Config
  records : List Record := []

def State.initial (config : Config := {}) : State := { config }

def work (cost : CostObservation) : Nat :=
  cost.arithmeticWork + cost.visitedEntries + cost.estimatedProofNodes

def ruleKey (invocation : InvocationKey) : Key := .invocation invocation

def offerKey? : OfferKey -> Option Key
  | .invoke invocation => some (.invocation invocation)
  | .equality equality => some (.equality equality)
  | .retry source effort => some (.invocation { source with effort })
  | .instantiate _ _ | .split _ _ _ _ => none

def find? (records : List Record) (key : Key) : Option Record :=
  records.find? fun record => record.key == key

def replace (records : List Record) (record : Record) : List Record :=
  record :: records.filter fun old => old.key != record.key

def alter (records : List Record) (key : Key) (change : Record -> Record) : List Record :=
  replace records (change ((find? records key).getD { key }))

def recordRule (records : List Record) (observation : RuleObservation Fact) : List Record :=
  alter records (.invocation observation.invocation) fun record =>
    { record with
      runs := record.runs + 1
      improvements := record.improvements + observation.changes.size
      noChanges := record.noChanges + if observation.outcome == .noChange then 1 else 0
      work := record.work + work observation.cost }

def recordEquality (records : List Record)
    (observation : EqualityObservation Fact) : List Record :=
  alter records (.equality observation.key) fun record =>
    { record with
      runs := record.runs + 1
      improvements := record.improvements + observation.changes.size
      noChanges := record.noChanges + if observation.outcome == .noChange then 1 else 0
      work := record.work + observation.narrowCalls }

def update : State -> Event Fact -> State
  | state, .rule observation =>
      { state with records := recordRule state.records observation }
  | state, .equality observation =>
      { state with records := recordEquality state.records observation }
  | state, .instance _ | state, .dismissed | state, .rejected _ |
      state, .invalidPayload _ | state, .rejectedPayload _ => state

/-- Learned benefit before fairness.  All arithmetic is deterministic `Nat`
arithmetic; subtraction saturates at zero. -/
def learnedScore (config : Config) (record : Option Record) (age : Nat) : Nat :=
  let ageBonus := Nat.min age config.ageBonusCap
  match record with
  | none => config.optimism + ageBonus
  | some record =>
      let gain := config.gainWeight * record.improvements / (record.work + record.runs + 1)
      gain + ageBonus - config.noChangePenalty * record.noChanges

structure Ranked where
  offer : OfferView
  fair : Bool
  stage : Nat
  score : Nat

def rankOffer (state : State) (offer : OfferView) : Ranked :=
  let record := (offerKey? offer.key).bind (find? state.records)
  { offer
    fair := state.config.fairnessAge <= offer.age
    stage := StagedPolicy.rank offer
    score := learnedScore state.config record offer.age }

/-- Fair offers form the first tier.  Within one tier the staged semantic class
still wins, then learned score, age, and finally stable input order. -/
def better (candidate current : Ranked) : Bool :=
  (candidate.fair && !current.fair) ||
    (candidate.fair == current.fair && candidate.stage < current.stage) ||
    (candidate.fair == current.fair && candidate.stage == current.stage &&
      (current.score < candidate.score ||
        (current.score == candidate.score && current.offer.age < candidate.offer.age)))

def choose? (state : State) (offers : Array OfferView) : Option OfferView :=
  (offers.foldl (fun best offer =>
    if !StagedPolicy.allowed state.config.staged offer then best
    else
      let candidate := rankOffer state offer
      match best with
      | none => some candidate
      | some current => if better candidate current then some candidate else best) none).map
    (fun ranked => ranked.offer)

def controller : TargetRun.Controller Fact State where
  update := update
  choose := fun state view =>
    match choose? state view.offers with
    | some offer => .select offer state
    | none => .stop state

end Hex.Interval.Experiment.AdaptivePolicy
