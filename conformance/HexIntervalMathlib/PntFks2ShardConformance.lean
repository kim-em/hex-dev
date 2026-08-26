/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntFks2Shard
import HexInterval.Experiment.Frontend
import HexInterval.Experiment.TargetRun

/-!
# PNT+ FKS2 shard conformance

Runs fifty bounded actions over all 1,000 source-pinned shard-11 cells, checks
exact coordinate diagnostics for a false mutation, and replays representative
first/middle/last cells by direct indexed schema dispatch.  The generic
large-payload `ProofFrontend` fold is deliberately not part of this probe.
-/

namespace Hex.IntervalMathlib.PntFks2ShardConformance

open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay
open Frontend PntFks2Shard

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts
    target := { node := node 999, fact := .nonnegative } }

private def run? : Option (TargetRun.Result Bound Unit) := do
  let .ok session := start | none
  some (TargetRun.drive factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  reached : TargetRun.Reached Bound
  events : Array (TargetRun.Event Bound)

def fixture? : Option Fixture := do
  let result ← run?
  let .target reached := result.stop | none
  some { session := result.session, reached, events := result.events }

#guard cells11.length == 1000
#guard chunkCount == 50
#guard (List.range chunkCount).all fun index => (chunk index).length == 20
#guard cells11[0]?.any fun cell => cell.b == 11010 && cell.b' == 11011
#guard cells11[989]?.any fun cell => cell.b == 11999 && cell.b' == 12000
#guard cells11[990]?.any fun cell => cell.b == 12000 && cell.b' == 12005
#guard cells11[999]?.any fun cell => cell.b == 12045 && cell.b' == 12050
#guard cells11.all checkCell

#guard run?.isSome
#guard fixture?.isSome
#guard fixture?.any fun fixture => fixture.events.size == 50
#guard fixture?.any fun fixture => fixture.session.state.engine.chronology.size == 1000
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.requests == 50
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.replies == 50
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.candidates == 1000
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.improvements == 1000
#guard fixture?.any fun fixture => fixture.session.arena.entries.size == 50
#guard fixture?.any fun fixture => fixture.session.arena.bodyCells == 8000
#guard limits.engine.maxNodes == 1001 && limits.engine.maxArity == 1000
#guard limits.arena.maxBodyCells == 8192 &&
  limits.arena.maxAtom == 100000000000000000000000000000000000000

def falseFirst : Cell :=
  ⟨11010, 11011, 4761/100000000000000000000000000000000000,
    5246427/50000, 2623333/25000⟩

def falseChunk : List Cell := falseFirst :: (chunk 0).drop 1

#guard firstFailure? falseChunk == some 11010
#guard decodeChunk? 0 (falseChunk.flatMap encodeCell) == none
#guard !(factFormat 0).validateBody (falseChunk.flatMap encodeCell)

/-- The doubled-`eps` mutation is mathematically false at its upper endpoint,
not a request for a finer enclosure. -/
theorem rejectFalseFirst : ¬ CellHolds falseFirst := by
  intro holds
  have endpoint := holds falseFirst.shi.value
    ⟨by norm_num [falseFirst, Q.value], le_rfl⟩
  let reduced : ℝ := (2119 / 320000 : ℝ) * (2623333 / 25000 : ℝ)
  have reducedNonnegative : 0 ≤ reduced := by
    norm_num [reduced]
  have lower := Real.sum_le_exp_of_nonneg reducedNonnegative 5
  have lowerNonnegative :
      0 ≤ ∑ degree ∈ Finset.range 5, reduced ^ degree / degree.factorial := by
    positivity
  have powered := pow_le_pow_left₀ lowerNonnegative lower 128
  rw [← Real.exp_nat_mul] at powered
  norm_num only [Nat.cast_ofNat] at powered
  norm_num [falseFirst, Q.value, aq] at endpoint
  have impossible := powered.trans endpoint
  norm_num at impossible

/--
info: 'Hex.IntervalMathlib.PntFks2ShardConformance.rejectFalseFirst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rejectFalseFirst

private def chunk0Action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := ruleKey 0
    node := batchNode
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := chunkNodes 0 }

private def request0 : RuleRequest Bound :=
  { action := chunk0Action
    program :=
      { programVersion := 0
        operations := program.operations
        nodes := program.nodes
        generations := Array.replicate 1001 0
        depths := Array.replicate 1001 0 }
    inputs := []
    writes := chunkNodes 0 }

#guard
  match (planCells 0 falseChunk request0).outcome with
  | .failed 11010 => true
  | _ => false
#guard (planCells 0 falseChunk request0).drafts.isEmpty

private def action (chunkIndex : Nat) : Action :=
  { serial := chunkIndex
    programVersion := 0
    application := { index := chunkIndex }
    rule := { index := chunkIndex }
    key := ruleKey chunkIndex
    node := batchNode
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := chunkNodes chunkIndex }

private def context (chunkIndex : Nat) (target : NodeId) :
    RuleFactContext checkerInput (action chunkIndex) :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node := target, fact := .nonnegative } }

#guard ((batchFactSchema 0).replay checkerInput
  (action 0) (context 0 (node 0)) ()).isSome
#guard ((batchFactSchema 25).replay checkerInput
  (action 25) (context 25 (node 500)) ()).isSome
#guard ((batchFactSchema 49).replay checkerInput
  (action 49) (context 49 (node 999)) ()).isSome
#guard ((batchFactSchema 0).replay checkerInput
  (action 0) (context 0 (node 20)) ()).isNone

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture =>
      Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard trace?.any fun trace =>
  trace.program == program && trace.events.length == 1000

/--
info: 'Hex.Interval.Experiment.PntFks2Shard.cells11_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cells11_checked

/-- Source-declaration-shaped arbitrary membership wrapper for the full shard. -/
theorem shard11Full (cell : Cell) (member : cell ∈ cells11) : CellHolds cell :=
  cells11_holds cell member

/--
info: 'Hex.IntervalMathlib.PntFks2ShardConformance.shard11Full' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shard11Full

end Hex.IntervalMathlib.PntFks2ShardConformance
