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
or package keys. It learns from observations attached to engine-authenticated
events: engine-derived fact-version changes and bounded, package-reported
logical work. Stable application sites retain useful history across changed
input versions, while the exact invocation snapshot prevents an old fixed
point from suppressing newly woken work.

The scores choose search order only.  Every selected offer is revalidated by
`PolicySession`, and proof replay is independent of this module.
-/

namespace Hex.Interval.Experiment.AdaptivePolicy

open Propagator Propagator.Policy TargetRun

/-- Replaceable integer coefficients for the first feedback experiment. -/
structure Config where
  staged : StagedPolicy.Config := {}
  optimism : Nat := 16
  gainWeight : Nat := 96
  noChangePenalty : Nat := 12
  ageBonusCap : Nat := 4
  fairnessAge : Nat := 20
  maxRecords : Nat := 256
  deriving DecidableEq, Repr

/-- Stable, package-opaque identity at which feedback is accumulated.  The
changing invocation snapshot is stored separately in `Record.last`. -/
inductive Key where
  | invocation (scope : ScopeId) (application : ApplicationId) (rule : RuleKey)
      (anchor : NodeId) (kind : ActionKind) (effort generation : Nat)
  | equality (scope : ScopeId) (equality : EqualityId)
  deriving DecidableEq

/-- The exact engine snapshot on which an observation was made. -/
inductive Snapshot where
  | invocation (invocation : InvocationKey)
  | equality (equality : EqualityWorkKey)
  deriving DecidableEq

/-- Bounded search observations accumulated for one selectable transition. -/
structure Record where
  key : Key
  runs : Nat := 0
  improvements : Nat := 0
  noChanges : Nat := 0
  /-- Consecutive fixed points on the exact last snapshot.  This resets when
  input versions change, so stale fixed points do not demote new work. -/
  stagnant : Nat := 0
  work : Nat := 0
  last : Option Snapshot := none

structure State where
  config : Config
  records : List Record := []

def State.initial (config : Config := {}) : State := { config }

/-- Package-reported deterministic work is a bounded scheduling hint, never
proof evidence or an engine-independent measurement. -/
def work (cost : CostObservation) : Nat :=
  cost.arithmeticWork + cost.visitedEntries + cost.estimatedProofNodes

def ruleKey (invocation : InvocationKey) : Key :=
  .invocation invocation.scope invocation.application invocation.rule invocation.anchor
    invocation.kind invocation.effort invocation.generation

def equalityKey (equality : EqualityWorkKey) : Key :=
  .equality equality.scope equality.equality

def offerKey? : OfferKey -> Option Key
  | .invoke invocation => some (ruleKey invocation)
  | .equality equality => some (equalityKey equality)
  | .retry source effort => some (ruleKey { source with effort })
  | .instantiate _ _ | .split _ _ _ _ => none

def offerSnapshot? : OfferKey -> Option Snapshot
  | .invoke invocation => some (.invocation invocation)
  | .equality equality => some (.equality equality)
  | .retry source effort => some (.invocation { source with effort })
  | .instantiate _ _ | .split _ _ _ _ => none

def find? (records : List Record) (key : Key) : Option Record :=
  records.find? fun record => record.key == key

def replace (limit : Nat) (records : List Record) (record : Record) : List Record :=
  (record :: records.filter fun old => old.key != record.key).take limit

def alter (limit : Nat) (records : List Record) (key : Key)
    (change : Record -> Record) : List Record :=
  replace limit records (change ((find? records key).getD { key }))

def recordRule (limit : Nat) (records : List Record)
    (observation : RuleObservation Fact) : List Record :=
  let snapshot := Snapshot.invocation observation.invocation
  alter limit records (ruleKey observation.invocation) fun record =>
    { record with
      runs := record.runs + 1
      improvements := record.improvements + observation.changes.size
      noChanges := record.noChanges + if observation.outcome == .noChange then 1 else 0
      stagnant := if observation.outcome != .noChange then 0
        else if record.last == some snapshot then record.stagnant + 1 else 1
      work := record.work + work observation.cost
      last := some snapshot }

def recordEquality (limit : Nat) (records : List Record)
    (observation : EqualityObservation Fact) : List Record :=
  let snapshot := Snapshot.equality observation.key
  alter limit records (equalityKey observation.key) fun record =>
    { record with
      runs := record.runs + 1
      improvements := record.improvements + observation.changes.size
      noChanges := record.noChanges + if observation.outcome == .noChange then 1 else 0
      stagnant := if observation.outcome != .noChange then 0
        else if record.last == some snapshot then record.stagnant + 1 else 1
      work := record.work + observation.narrowCalls
      last := some snapshot }

def update : State -> Event Fact -> State
  | state, .rule observation =>
      { state with records := recordRule state.config.maxRecords state.records observation }
  | state, .equality observation =>
      { state with records := recordEquality state.config.maxRecords state.records observation }
  | state, .instance _ | state, .dismissed | state, .rejected _ |
      state, .invalidPayload _ | state, .rejectedPayload _ => state

/-- Learned benefit before fairness.  All arithmetic is deterministic `Nat`
arithmetic; subtraction saturates at zero. -/
def learnedScore (config : Config) (record : Option Record)
    (snapshot : Option Snapshot) (age : Nat) : Nat :=
  let ageBonus := Nat.min age config.ageBonusCap
  match record with
  | none => config.optimism + ageBonus
  | some record =>
      let gain := config.gainWeight * record.improvements / (record.work + record.runs + 1)
      if record.last != snapshot then Nat.max config.optimism gain + ageBonus
      else gain + ageBonus - config.noChangePenalty * record.stagnant

structure Ranked where
  offer : OfferView
  fair : Bool
  stage : Nat
  score : Nat

def rankOffer (state : State) (offer : OfferView) : Ranked :=
  let record := (offerKey? offer.key).bind (find? state.records)
  let snapshot := offerSnapshot? offer.key
  { offer
    fair := state.config.fairnessAge <= offer.age
    stage := StagedPolicy.rank offer
    score := learnedScore state.config record snapshot offer.age }

/-- Offers at or beyond `fairnessAge` form the first tier.  On a finite frontier,
selection consumes offers, so this tier ensures every continuously eligible
offer is eventually sampled.  Within one tier the staged semantic class still
wins, then learned score, age, and finally stable input order. -/
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
