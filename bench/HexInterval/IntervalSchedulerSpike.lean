/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Propagator

public section

/-!
# Logical-count spike for interval propagation scheduling

This benchmark compares two schedulers after one input in an already-saturated
forest of unary expression chains is strengthened.

* `runIncremental` uses `Experiment.Propagator.Engine`: only applications
  watching a changed fact enter the worklist.
* `runStructural` repeatedly scans every compiled application until one whole
  scan makes no change.

The operations and rule keys are deliberately opaque to both schedulers.  A
small external registry gives the two alternating unary operations the same
benchmark behavior, `output := input + 1`.  `Nat` is only a monotone fact rank;
this file exercises no rational or endpoint arithmetic.

The primary measurements are deterministic rule-invocation and improvement
counts.  A position-sensitive checksum pins the final facts, so a lower count
cannot be obtained by silently skipping propagation.  Wall-clock timing can be
layered on this module later without changing the logical workload.
-/

namespace Hex.Interval.Experiment.Propagator.Bench

/-! # Opaque unary forest fixture -/

def rankDomain : DomainId := { index := 0 }

def inputKey : OpKey := { name := "scheduler-spike.input" }

def unaryFKey : OpKey := { name := "scheduler-spike.f" }

def unaryGKey : OpKey := { name := "scheduler-spike.g" }

def operations : Array Operation :=
  #[{ key := inputKey, inputs := [], output := rankDomain },
    { key := unaryFKey, inputs := [rankDomain], output := rankDomain },
    { key := unaryGKey, inputs := [rankDomain], output := rankDomain }]

def rules : Array Registration :=
  #[{ key := { name := "scheduler-spike.f-forward" }
      head := unaryFKey
      kind := .forward
      watches := [.argument 0]
      writes := [.result] },
    { key := { name := "scheduler-spike.g-forward" }
      head := unaryGKey
      kind := .forward
      watches := [.argument 0]
      writes := [.result] }]

/-- `trees` disconnected chains, each with one input and `depth` alternating
opaque unary applications. -/
def forestProgram (trees depth : Nat) : Program := Id.run do
  let mut nodes := #[]
  for _tree in [0:trees] do
    let root : NodeId := { index := nodes.size }
    nodes := nodes.push { domain := rankDomain, op := { index := 0 }, args := [] }
    let mut previous := root
    for level in [0:depth] do
      let operation : OpId := { index := if level % 2 = 0 then 1 else 2 }
      let output : NodeId := { index := nodes.size }
      nodes := nodes.push { domain := rankDomain, op := operation, args := [previous] }
      previous := output
  return { operations, nodes }

/-- Facts at the old fixed point: each chain contains ranks `0, 1, ..., depth`.
The benchmark subsequently raises the first root from zero to one. -/
def saturatedFacts (trees depth : Nat) : Array Nat := Id.run do
  let mut facts := #[]
  for _tree in [0:trees] do
    facts := facts.push 0
    for level in [0:depth] do
      facts := facts.push (level + 1)
  return facts

def firstRoot : NodeId := { index := 0 }

/-- Raise the selected input without scheduling anything. -/
def refineFirstRoot (facts : Array Nat) : Option (Array Nat) := do
  let _ <- facts[firstRoot.index]?
  return facts.set! firstRoot.index 1

def applicationCount (trees depth : Nat) : Nat := trees * depth

def generousLimits (trees depth : Nat) : Limits :=
  let nodeCount := trees * (depth + 1)
  let applications := applicationCount trees depth
  { maxOperations := operations.size
    maxNodes := nodeCount
    maxRules := rules.size
    maxRegistryEntries := operations.size + rules.size
    maxReplayFormats := 0
    maxArity := 1
    maxApplications := applications
    maxQueueEntries := applications + nodeCount + 1
    maxActions := applications + nodeCount + 1
    maxAcceptedFacts := applications + nodeCount + 1
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 1
    maxDiagnosticValue := 1
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 0
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := nodeCount
    maxEqualities := 0
    splitEndpointLimit := { maxEndpointHeight := 64, maxAlignmentShift := 64 } }

/-! # Shared workload and observables -/

/-- Larger `Nat` facts are stronger. -/
def factDomain : FactDomain Nat where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

/-- Position-sensitive final-state checksum. -/
def factsChecksum (facts : Array Nat) : Nat := Id.run do
  let mut checksum := 0
  for index in [0:facts.size] do
    checksum := checksum + (index + 1) * (facts[index]! + 1)
  return checksum

inductive Stop where
  | saturated
  | setupFailure
  | engineFailure
  | fuel
  deriving DecidableEq, Repr

structure LogicalResult where
  stop : Stop
  invocations : Nat
  improvements : Nat
  sweeps : Nat
  checksum : Nat
  deriving DecidableEq, Repr

structure Comparison where
  incremental : LogicalResult
  structural : LogicalResult
  deriving DecidableEq, Repr

/-- The registry owns the meaning of both opaque unary rule keys.  The
scheduler sees only one declared input and one result candidate. -/
def invokeUnary (invocations : Nat) (request : RuleRequest Nat) : Outcome Nat × Nat :=
  let nextInvocations := invocations + 1
  match request.inputs, request.writes with
  | [input], [output] =>
      (.success
        [{ node := output
           fact := input.fact + 1
           payload := { index := invocations } }]
        [] { arithmeticWork := 1, visitedEntries := 1, estimatedProofNodes := 1 },
        nextInvocations)
  | _, _ => (.failed 1, nextInvocations)

def stopOfRun : RunStop -> Stop
  | .saturated => .saturated
  | .driverFuel => .fuel
  | .contradiction | .engineResource _ | .factResource _ | .invalidReply _ |
      .invalidEngine => .engineFailure

/-- Clear the initial all-rules queue to model an old fixed point, install one
new source fact, and wake exactly that source's watchers. -/
def prepareIncremental (trees depth : Nat) : Option (Engine Nat) := do
  if trees = 0 then none else pure ()
  let initial <-
    match Engine.start factDomain (forestProgram trees depth) rules (saturatedFacts trees depth)
        (generousLimits trees depth) with
    | .ok state => some state
    | .error _ => none
  let facts <- refineFirstRoot initial.facts
  let idle : Engine Nat :=
    { initial with
      facts
      versions := initial.versions.set! firstRoot.index 1
      queue := #[]
      queueHead := 0
      queued := Array.replicate initial.applications.size false
      metrics := {} }
  match idle.wakeNode firstRoot with
  | .ok ready => some ready
  | .error _ => none

/-- Dependency-indexed propagation after one local input refinement. -/
def runIncremental (trees depth : Nat) : LogicalResult :=
  match prepareIncremental trees depth with
  | none =>
      { stop := .setupFailure
        invocations := 0
        improvements := 0
        sweeps := 0
        checksum := 0 }
  | some initial =>
      let result := drive invokeUnary (depth + 1) initial 0
      { stop := stopOfRun result.stop
        invocations := result.state.metrics.requests
        improvements := result.state.metrics.improvements
        sweeps := 0
        checksum := factsChecksum result.state.facts }

/-! # Whole-network structural baseline -/

structure ScanState where
  facts : Array Nat
  invocations : Nat := 0
  improvements : Nat := 0
  sweeps : Nat := 0

/-- Invoke every compiled unary application once, in SSA order. -/
def scanOnce (applications : Array Application) (state : ScanState) : Option (ScanState × Bool) := do
  let mut facts := state.facts
  let mut invocations := state.invocations
  let mut improvements := state.improvements
  let mut changed := false
  for index in [0:applications.size] do
    let application <- applications[index]?
    let input <- application.watches[0]?
    let current <- facts[application.node.index]?
    let inputFact <- facts[input.index]?
    let candidate := inputFact + 1
    invocations := invocations + 1
    if current < candidate then
      facts := facts.set! application.node.index candidate
      improvements := improvements + 1
      changed := true
  return ({ facts, invocations, improvements, sweeps := state.sweeps + 1 }, changed)

def scanToFixedPoint : Nat -> Array Application -> ScanState -> LogicalResult
  | 0, _, state =>
      { stop := .fuel
        invocations := state.invocations
        improvements := state.improvements
        sweeps := state.sweeps
        checksum := factsChecksum state.facts }
  | fuel + 1, applications, state =>
      match scanOnce applications state with
      | none =>
          { stop := .engineFailure
            invocations := state.invocations
            improvements := state.improvements
            sweeps := state.sweeps
            checksum := factsChecksum state.facts }
      | some (next, true) => scanToFixedPoint fuel applications next
      | some (next, false) =>
          { stop := .saturated
            invocations := next.invocations
            improvements := next.improvements
            sweeps := next.sweeps
            checksum := factsChecksum next.facts }

/-- Baseline which has no dependency index: every non-final sweep invokes all
applications, and a final all-network sweep is required to detect saturation. -/
def runStructural (trees depth : Nat) : LogicalResult :=
  if trees = 0 then
    { stop := .setupFailure
      invocations := 0
      improvements := 0
      sweeps := 0
      checksum := 0 }
  else
    match compileApplications (forestProgram trees depth) rules,
        refineFirstRoot (saturatedFacts trees depth) with
    | some applications, some facts =>
        scanToFixedPoint (depth + 2) applications { facts }
    | _, _ =>
        { stop := .setupFailure
          invocations := 0
          improvements := 0
          sweeps := 0
          checksum := 0 }

def compare (trees depth : Nat) : Comparison :=
  { incremental := runIncremental trees depth
    structural := runStructural trees depth }

/-! # Exact logical-count formulas -/

def expectedIncrementalInvocations (depth : Nat) : Nat := depth

def expectedStructuralInvocations (trees depth : Nat) : Nat :=
  if depth = 0 then 0 else 2 * applicationCount trees depth

def expectedSweeps (depth : Nat) : Nat := if depth = 0 then 1 else 2

/-- Direct construction of the expected fixed point, kept independent of both
schedulers for checksum validation. -/
def expectedFacts (trees depth : Nat) : Array Nat := Id.run do
  let mut facts := #[]
  for tree in [0:trees] do
    for level in [0:depth + 1] do
      facts := facts.push (if tree = 0 then level + 1 else level)
  return facts

def comparisonValid (trees depth : Nat) (comparison : Comparison) : Bool :=
  0 < trees && comparison.incremental.stop == .saturated &&
    comparison.structural.stop == .saturated &&
    comparison.incremental.invocations == expectedIncrementalInvocations depth &&
    comparison.structural.invocations == expectedStructuralInvocations trees depth &&
    comparison.incremental.improvements == depth &&
    comparison.structural.improvements == depth &&
    comparison.structural.sweeps == expectedSweeps depth &&
    comparison.incremental.checksum == comparison.structural.checksum &&
    comparison.incremental.checksum == factsChecksum (expectedFacts trees depth)

/-- Small reduction canary.  Four depth-eight chains require eight incremental
calls versus sixty-four calls for structural rescanning. -/
def canary : Comparison := compare 4 8

/-- Suggested logical-count corpus.  Increasing the disconnected-tree count
leaves incremental work fixed at `depth`, while structural work grows as
`2 * trees * depth`. -/
def corpus : Array (Nat × Nat × Comparison) :=
  #[(1, 64, compare 1 64),
    (8, 64, compare 8 64),
    (64, 64, compare 64 64),
    (256, 32, compare 256 32)]

end Hex.Interval.Experiment.Propagator.Bench

open Hex.Interval.Experiment.Propagator.Bench

def main : IO Unit := do
  if !comparisonValid 4 8 canary then
    throw (IO.userError "interval scheduler canary failed")
  IO.println s!"incremental calls: {canary.incremental.invocations}"
  IO.println s!"structural calls: {canary.structural.invocations}"
  IO.println s!"shared checksum: {canary.incremental.checksum}"
