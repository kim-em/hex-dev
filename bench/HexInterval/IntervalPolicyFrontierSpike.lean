/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Policy

/-!
# Policy-frontier representation spike

This benchmark compares two ways of exposing the same engine-owned semantic
offers to an external policy after one local fact improvement.

* `runScan` uses the current complete `Policy.State.view`.  Every decision and
  the final saturation check traverse all application, equality, and
  suggestion slots.
* `runDirect` adapts each new engine work event directly to an `OfferId`, then
  asks `Policy.State.offer?` for the current semantic offer.  Selection still
  crosses the same engine validation boundary; the adapter cannot manufacture
  an action.

The workload is a forest of disconnected chains of opaque unary operations.
Facts are monotone `Nat` ranks, and the external registry gives both operation
keys the same behavior, `output := input + 1`.  Thus this file measures policy
frontier discovery rather than endpoint or rational arithmetic.

Both representations must make the same decisions, invoke the same arbitrary
propagators, and produce the same final facts and position-sensitive checksum.
The primary evidence is the exact logical frontier-visit count.  Wall time is
reported only after those equalities and count formulas have been checked.
-/

namespace Hex.Interval.Experiment.Propagator.PolicyFrontierBench

open Policy

abbrev Rank := Nat

/-! ## Opaque generic-propagator workload -/

def rankDomainId : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "policy-frontier.source" }

def unaryFKey : OpKey := { name := "policy-frontier.f" }

def unaryGKey : OpKey := { name := "policy-frontier.g" }

def operations : Array Operation :=
  #[{ key := sourceKey, inputs := [], output := rankDomainId },
    { key := unaryFKey, inputs := [rankDomainId], output := rankDomainId },
    { key := unaryGKey, inputs := [rankDomainId], output := rankDomainId }]

def rules : Array Registration :=
  #[{ key := { name := "policy-frontier.f-forward" }
      head := unaryFKey
      kind := .forward
      watches := [.argument 0]
      writes := [.result] },
    { key := { name := "policy-frontier.g-forward" }
      head := unaryGKey
      kind := .forward
      watches := [.argument 0]
      writes := [.result] }]

/-- `trees` disconnected chains, each with one source and `depth` opaque unary
applications.  Alternating operation keys ensures that the scheduler is not
silently relying on one distinguished function. -/
def forestProgram (trees depth : Nat) : Program := Id.run do
  let mut nodes := #[]
  for _tree in [0:trees] do
    let root : NodeId := { index := nodes.size }
    nodes := nodes.push
      { domain := rankDomainId, op := { index := 0 }, args := [] }
    let mut previous := root
    for level in [0:depth] do
      let operation : OpId := { index := if level % 2 = 0 then 1 else 2 }
      let output : NodeId := { index := nodes.size }
      nodes := nodes.push
        { domain := rankDomainId, op := operation, args := [previous] }
      previous := output
  return { operations, nodes }

/-- Facts at the old fixed point: every chain stores ranks
`0, 1, ..., depth`. -/
def saturatedFacts (trees depth : Nat) : Array Rank := Id.run do
  let mut facts := #[]
  for _tree in [0:trees] do
    for level in [0:depth + 1] do
      facts := facts.push level
  return facts

def firstRoot : NodeId := { index := 0 }

def applicationCount (trees depth : Nat) : Nat := trees * depth

/-- Larger ranks are strictly stronger synthetic facts. -/
def rankDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

def engineLimits (trees depth : Nat) : Experiment.Propagator.Limits :=
  let nodes := trees * (depth + 1)
  let applications := applicationCount trees depth
  { maxOperations := operations.size
    maxNodes := nodes
    maxRules := rules.size
    maxArity := 1
    maxApplications := applications
    maxQueueEntries := applications + 1
    maxActions := depth + 1
    maxAcceptedFacts := depth + 1
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 1
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 0
    maxInstances := 0
    maxGeneration := 0
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 1, maxAlignmentShift := 0 } }

def expectedScanVisits (trees depth : Nat) : Nat :=
  applicationCount trees depth * (depth + 1)

def policyLimits (trees depth : Nat) : Policy.Limits :=
  { maxDecisions := depth + 1
    maxTraversal := expectedScanVisits trees depth
    maxLiveOffers := applicationCount trees depth }

/-- Start from an already-saturated forest, strengthen only the first source,
and retain only the resulting dependency event.  Clearing the engine's initial
all-applications queue makes both frontier measurements start at the same
local-refinement boundary. -/
def prepare (trees depth : Nat) : Option (Policy.State Rank) := do
  if trees = 0 then none else pure ()
  let initial <-
    match Engine.start rankDomain (forestProgram trees depth) rules
        (saturatedFacts trees depth) (engineLimits trees depth) with
    | .ok engine => some engine
    | .error _ => none
  let _ <- initial.facts[firstRoot.index]?
  let idle : Engine Rank :=
    { initial with
      facts := initial.facts.set! firstRoot.index 1
      versions := initial.versions.set! firstRoot.index 1
      queue := #[]
      queueHead := 0
      queued := Array.replicate initial.applications.size false
      metrics := {} }
  let ready <- match idle.wakeNode firstRoot with
    | .ok engine => some engine
    | .error _ => none
  some (Policy.State.start ready (policyLimits trees depth))

/-! ## Shared selection and observations -/

/-- The registry, rather than the scheduler, supplies the semantics of both
opaque unary rule keys. -/
def invokeUnary (request : RuleRequest Rank) : Outcome Rank :=
  match request.inputs, request.writes with
  | [input], [output] =>
      .success
        [{ node := output
           fact := input.fact + 1
           payload := { index := request.action.serial } }]
        []
        { arithmeticWork := 1, visitedEntries := 1, estimatedProofNodes := 1 }
  | _, _ => .failed 1

/-- Execute one engine-issued semantic offer through the validated selection
and request/reply boundaries. -/
def executeOffer? (state : Policy.State Rank) (offer : OfferView) : Option (Policy.State Rank) :=
  let selection : Selection :=
    { scope := state.scope
      serial := state.serial
      programVersion := state.engine.programVersion
      id := offer.id
      expected := offer.key }
  match state.select selection with
  | .request request awaiting =>
      match awaiting.submit (request.action.reply (invokeUnary request)) with
      | .accepted _ next => some next
      | _ => none
  | _ => none

/-- Position-sensitive checksum of all final facts. -/
def factsChecksum (facts : Array Rank) : Nat := Id.run do
  let mut checksum := 0
  for index in [0:facts.size] do
    checksum := checksum + (index + 1) * (facts[index]! + 1)
  return checksum

/-- Independent construction of the expected fixed point. -/
def expectedFacts (trees depth : Nat) : Array Rank := Id.run do
  let mut facts := #[]
  for tree in [0:trees] do
    for level in [0:depth + 1] do
      facts := facts.push (if tree = 0 then level + 1 else level)
  return facts

inductive Stop where
  | saturated
  | setupFailure
  | frontierResource
  | invalidTransition
  | fuel
  deriving DecidableEq, Repr

structure LogicalResult where
  stop : Stop
  frontierVisits : Nat
  decisions : Nat
  invocations : Nat
  improvements : Nat
  facts : Array Rank
  checksum : Nat
  deriving DecidableEq, Repr

def result (stop : Stop) (frontierVisits : Nat) (state : Policy.State Rank) : LogicalResult :=
  { stop
    frontierVisits
    decisions := state.metrics.decisions
    invocations := state.engine.metrics.requests
    improvements := state.engine.metrics.improvements
    facts := state.engine.facts
    checksum := factsChecksum state.engine.facts }

def failedResult (stop : Stop) : LogicalResult :=
  { stop
    frontierVisits := 0
    decisions := 0
    invocations := 0
    improvements := 0
    facts := #[]
    checksum := 0 }

/-! ## Complete frontier scan -/

def scanLoop : Nat -> Policy.State Rank -> LogicalResult
  | 0, state => result .fuel state.metrics.traversal state
  | fuel + 1, state =>
      match state.view with
      | .error _ => result .frontierResource state.metrics.traversal state
      | .ok (view, scanned) =>
          match view.offers[0]? with
          | none => result .saturated scanned.metrics.traversal scanned
          | some offer =>
              match executeOffer? scanned offer with
              | none => result .invalidTransition scanned.metrics.traversal scanned
              | some next => scanLoop fuel next

/-- Current reference policy path: construct a complete bounded view before
every choice and once more to establish saturation. -/
@[noinline]
def runScanPrepared (state : Policy.State Rank) (depth : Nat) : LogicalResult :=
  scanLoop (depth + 2) state

def runScan (trees depth : Nat) : LogicalResult :=
  match prepare trees depth with
  | none => failedResult .setupFailure
  | some state => runScanPrepared state depth

/-! ## Event-indexed semantic-offer adapter -/

def offerIdOfWork : WorkItem -> OfferId
  | .application application => .application application
  | .equality equality => .equality equality

def noDirtyWork (state : Policy.State Rank) : Bool :=
  !state.engine.queued.any id && !state.engine.equalityQueued.any id &&
    state.engine.suggestions.isEmpty && state.engine.pending.isNone

/-- Follow the append-only dependency-event log by exact index.  Every event
is converted to a semantic `OfferId` and re-read through `State.offer?`; this
does not hand a raw engine action to the external policy. -/
def directLoop : Nat -> Nat -> Nat -> Policy.State Rank -> LogicalResult
  | 0, _, visits, state => result .fuel visits state
  | fuel + 1, cursor, visits, state =>
      if state.engine.queue.size <= cursor then
        if noDirtyWork state then result .saturated visits state
        else result .invalidTransition visits state
      else
        match state.engine.queue[cursor]? with
        | none => result .invalidTransition visits state
        | some work =>
            let visits := visits + 1
            match state.offer? (offerIdOfWork work) with
            | none => directLoop fuel (cursor + 1) visits state
            | some offer =>
                match executeOffer? state offer with
                | none => result .invalidTransition visits state
                | some next => directLoop fuel (cursor + 1) visits next

/-- Candidate frontier representation: adapt only emitted work events to
semantic offers, while retaining the same selection revalidation. -/
@[noinline]
def runDirectPrepared (state : Policy.State Rank) (depth : Nat) : LogicalResult :=
  directLoop (depth + 2) 0 0 state

def runDirect (trees depth : Nat) : LogicalResult :=
  match prepare trees depth with
  | none => failedResult .setupFailure
  | some state => runDirectPrepared state depth

structure Comparison where
  scan : LogicalResult
  direct : LogicalResult
  deriving DecidableEq, Repr

def compareFrontiers (trees depth : Nat) : Comparison :=
  { scan := runScan trees depth, direct := runDirect trees depth }

def comparePrepared (state : Policy.State Rank) (depth : Nat) : Comparison :=
  { scan := runScanPrepared state depth, direct := runDirectPrepared state depth }

def expectedDirectVisits (depth : Nat) : Nat := depth

def resultValid (trees depth : Nat) (comparison : Comparison) : Bool :=
  0 < trees && comparison.scan.stop == .saturated &&
    comparison.direct.stop == .saturated &&
    comparison.scan.frontierVisits == expectedScanVisits trees depth &&
    comparison.direct.frontierVisits == expectedDirectVisits depth &&
    comparison.scan.decisions == depth && comparison.direct.decisions == depth &&
    comparison.scan.invocations == depth && comparison.direct.invocations == depth &&
    comparison.scan.improvements == depth && comparison.direct.improvements == depth &&
    comparison.scan.facts == comparison.direct.facts &&
    comparison.scan.facts == expectedFacts trees depth &&
    comparison.scan.checksum == comparison.direct.checksum &&
    comparison.scan.checksum == factsChecksum (expectedFacts trees depth)

/-! ## Compiled timing driver -/

def mix (acc value : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + value + 0xBF58476D1CE4E5B9

def stopCode : Stop -> Nat
  | .saturated => 1
  | .setupFailure => 2
  | .frontierResource => 3
  | .invalidTransition => 4
  | .fuel => 5

def observe (acc : UInt64) (iteration : Nat) (value : LogicalResult) : UInt64 :=
  mix
    (mix
      (mix
        (mix
          (mix
            (mix acc (UInt64.ofNat iteration))
            (UInt64.ofNat (stopCode value.stop)))
          (UInt64.ofNat value.frontierVisits))
        (UInt64.ofNat value.decisions))
      (UInt64.ofNat value.invocations))
    (UInt64.ofNat (value.improvements + value.checksum))

/-- Time only repeated policy runs from one prevalidated immutable snapshot;
program construction and application compilation stay outside the timed loop. -/
def timeMode (mode : String) (trees depth repeats : Nat)
    (initial : Policy.State Rank) (expected : LogicalResult)
    (work : Policy.State Rank -> Nat -> LogicalResult) : IO Bool := do
  let mut sink : UInt64 := 0
  for iteration in [0:4] do
    let value := work initial depth
    if value != expected then
      IO.eprintln s!"{mode}: warmup changed the logical result"
      return false
    sink := observe sink iteration value
  let start <- IO.monoNanosNow
  for iteration in [0:repeats] do
    let value := work initial depth
    sink := observe sink iteration value
  let stop <- IO.monoNanosNow
  IO.println <|
    s!"{mode} {trees} {depth} {applicationCount trees depth} {repeats} " ++
      s!"{stop - start} {expected.frontierVisits} {expected.decisions} " ++
      s!"{expected.invocations} {expected.improvements} {expected.checksum} {sink}"
  return true

def usage : String :=
  "usage: hex_interval_policy_frontier_spike TREES DEPTH REPEATS"

end Hex.Interval.Experiment.Propagator.PolicyFrontierBench

open Hex.Interval.Experiment.Propagator.PolicyFrontierBench

def main (args : List String) : IO UInt32 := do
  match args with
  | [treesText, depthText, repeatsText] =>
      let some trees := treesText.toNat? | IO.eprintln usage; return 2
      let some depth := depthText.toNat? | IO.eprintln usage; return 2
      let some repeats := repeatsText.toNat? | IO.eprintln usage; return 2
      if trees = 0 || repeats = 0 then
        IO.eprintln usage
        return 2
      let some initial := prepare trees depth
        | IO.eprintln "policy-frontier setup failed"
          return 2
      let comparison := comparePrepared initial depth
      if !resultValid trees depth comparison then
        IO.eprintln "policy-frontier logical canary failed"
        return 2
      let scanOk <-
        timeMode "scan" trees depth repeats initial comparison.scan runScanPrepared
      let directOk <-
        timeMode "direct" trees depth repeats initial comparison.direct runDirectPrepared
      return if scanOk && directOk then 0 else 2
  | _ =>
      IO.eprintln usage
      return 2
