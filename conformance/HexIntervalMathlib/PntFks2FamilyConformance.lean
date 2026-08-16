/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntFks2Family
import HexInterval.Experiment.Frontend
import HexInterval.Experiment.TargetRun

/-!
# Local/release conformance for the full PNT+ FKS2 family

This target is intentionally separate from merge-gating `HexConformance`.
It runs all 680 bounded actions over 13,590 source-pinned cells, checks
cross-shard dispatch and exact failure coordinates, and kernel-replays
representative cells from both sides of shard boundaries.
-/

namespace Hex.IntervalMathlib.PntFks2FamilyConformance

open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay
open Frontend PntFks2Family
open PntFks2Shard (Bound Cell CellHolds Q aq checkCell encodeCell factDomain)

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts
    target := { node := node (familyCellCount - 1), fact := .nonnegative } }

private def run? : Option (TargetRun.Result Bound Unit) := do
  let .ok session := start | none
  some (TargetRun.drive factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  reached : TargetRun.Reached Bound
  events : Array (TargetRun.Event Bound)
  trace : Frontend.Trace Bound

def fixture? : Option Fixture := do
  let result ← run?
  let .target reached := result.stop | none
  match Frontend.trace? result.session.state.engine result.session.arena with
  | none => none
  | some trace =>
      some { session := result.session, reached, events := result.events, trace }

#guard shardRecords.length == 14
#guard shardRecords.all fun record =>
  record.cells == if record.shard == 13 then 590 else 1000
#guard allCells.length == familyCellCount
#guard familyCellCount == 13590
#guard familyChunkCount == 680
#guard (List.range familyChunkCount).all fun index =>
  (familyChunk index).length == if index == 679 then 10 else 20
#guard allCells[0]?.any fun cell => cell.b == 10 && cell.b' == 11
#guard allCells[999]?.any fun cell => cell.b == 1009 && cell.b' == 1010
#guard allCells[1000]?.any fun cell => cell.b == 1010 && cell.b' == 1011
#guard allCells[10999]?.any fun cell => cell.b == 11009 && cell.b' == 11010
#guard allCells[11000]?.any fun cell => cell.b == 11010 && cell.b' == 11011
#guard allCells[13589]?.any fun cell => cell.b == 19995 && cell.b' == 20000
#guard allCells.all checkCell

#guard fixture?.any fun fixture =>
  fixture.events.size == 680 &&
  fixture.session.state.engine.chronology.size == 13590 &&
  fixture.session.state.engine.metrics.requests == 680 &&
  fixture.session.state.engine.metrics.replies == 680 &&
  fixture.session.state.engine.metrics.candidates == 13590 &&
  fixture.session.state.engine.metrics.improvements == 13590 &&
  fixture.session.arena.entries.size == 680 &&
  fixture.session.arena.bodyCells == 109400 &&
  fixture.trace.program == program &&
  fixture.trace.events.length == familyCellCount
#guard limits.engine.maxOutcomeCandidates == 20
#guard limits.arena.maxDrafts == 20 && limits.arena.maxDraftCells == 161
#guard limits.arena.maxBodyCells == 110000

def falseCell00 : Cell :=
  ⟨10, 11, 1000, 316227/100000, 331663/100000⟩

def falseChunk00 : List Cell := falseCell00 :: (familyChunk 0).drop 1

#guard firstFailure? 0 falseChunk00 == some 10
#guard decodeCoordinate 10 == (0, 10)
#guard decodeChunk? 0 (0 :: falseChunk00.flatMap encodeCell) == none
#guard decodeChunk? 50 (chunkBody 0) == none
#guard !(factFormat 50).validateBody (chunkBody 0)

/-- The false source cell contradicts its endpoint inequality; it cannot be
repaired by more precision. -/
theorem rejectFalseCell00 : ¬ CellHolds falseCell00 := by
  intro holds
  have endpoint := holds falseCell00.shi.value
    ⟨by norm_num [falseCell00, Q.value], le_rfl⟩
  have oneLe :
      (1 : ℝ) ≤ Real.exp ((2119 / 2500 : ℝ) * falseCell00.shi.value) := by
    exact Real.one_le_exp (by norm_num [falseCell00, Q.value])
  have rhsLt :
      aq.value / falseCell00.eps.value * falseCell00.shi.value ^ 3 < 1 := by
    norm_num [falseCell00, Q.value, aq]
  linarith

/--
info: 'Hex.IntervalMathlib.PntFks2FamilyConformance.rejectFalseCell00' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rejectFalseCell00

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

private def request (chunkIndex : Nat) : RuleRequest Bound :=
  { action := action chunkIndex
    program :=
      { programVersion := 0
        operations := program.operations
        nodes := program.nodes
        generations := Array.replicate (familyCellCount + 1) 0
        depths := Array.replicate (familyCellCount + 1) 0 }
    inputs := []
    writes := chunkNodes chunkIndex }

#guard
  match (planCells 0 falseChunk00 (request 0)).outcome with
  | .failed 10 => true
  | _ => false
#guard (planCells 0 falseChunk00 (request 0)).drafts.isEmpty

private def context (chunkIndex : Nat) (target : NodeId) :
    RuleFactContext checkerInput (action chunkIndex) :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node := target, fact := .nonnegative } }

#guard ((batchFactSchema 0).replay checkerInput
  (action 0) (context 0 (node 0)) ()).isSome
#guard ((batchFactSchema 49).replay checkerInput
  (action 49) (context 49 (node 999)) ()).isSome
#guard ((batchFactSchema 50).replay checkerInput
  (action 50) (context 50 (node 1000)) ()).isSome
#guard ((batchFactSchema 549).replay checkerInput
  (action 549) (context 549 (node 10999)) ()).isSome
#guard ((batchFactSchema 550).replay checkerInput
  (action 550) (context 550 (node 11000)) ()).isSome
#guard ((batchFactSchema 679).replay checkerInput
  (action 679) (context 679 (node 13589)) ()).isSome
#guard ((batchFactSchema 50).replay checkerInput
  (action 50) (context 50 (node 999)) ()).isNone

/-- Source-declaration-shaped arbitrary membership wrapper for all shards. -/
theorem familyFull (cell : Cell) (member : cell ∈ allCells) : CellHolds cell :=
  allCells_holds cell member

/--
info: 'Hex.Interval.Experiment.PntFks2Family.allCells_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allCells_checked

/--
info: 'Hex.IntervalMathlib.PntFks2FamilyConformance.familyFull' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms familyFull

end Hex.IntervalMathlib.PntFks2FamilyConformance

def main : IO Unit := pure ()
