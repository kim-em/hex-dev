/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable10Convex
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# PNT+ Table 10 convex-row batch conformance

The single bounded action authenticates rows 60–85 and installs all thirty
coordinate facts.  Endpoint, coordinate, and row-order mutations are rejected
without a draft or precision retry.
-/

namespace Hex.IntervalMathlib.PntTable10ConvexConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntTable10Convex

abbrev Bound := PntTable10Shard.Bound
abbrev Decimal := PntTable10Shard.Decimal
abbrev Coordinate := PntTable10Shard.Coordinate
abbrev Cell := PntTable10Shard.Cell

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts
    target := { node := node 29, fact := .upper row85.cell5 } }

private def run? : Option (TargetRun.Result Bound Unit) := do
  let .ok session := start | none
  some (TargetRun.drive PntTable10Shard.factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name

def fixture? : Option Fixture := do
  let result ← run?
  let .ok registry := ProofRegistry.build result.session.registry proofPackages | none
  some { session := result.session, registry }

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard validRows rows
#guard rows.length == 6
#guard cells.length == 30
#guard body.length == 216
#guard decodeRows? body == some rows
#guard decodeBatch? body == some ()
#guard expectedCandidates.length == 30
#guard row60.row == 60 && row60.nextRow == 65
#guard row85.row == 85 && row85.nextRow == 90
#guard row60.cell1.listed == PntTable10Shard.decimal 79446 14
#guard row85.cell5.listed == PntTable10Shard.decimal 15171 6
#guard run?.isSome
#guard fixture?.isSome
#guard fixture?.any fun fixture => fixture.session.state.engine.chronology.size == 30
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.requests == 1
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.candidates == 30
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.improvements == 30
#guard fixture?.any fun fixture => fixture.session.arena.entries.size == 1
#guard fixture?.any fun fixture =>
  fixture.registry.emit.find? batchFactSchema.key == some ``batchFactSchema

private def mutationAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := ruleKey
    node := batchNode
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := cellNodes }

private def programView : ProgramView :=
  { programVersion := 0
    operations := program.operations
    nodes := program.nodes
    generations := Array.replicate 31 0
    depths := (Array.replicate 30 0).push 1 }

private def request : RuleRequest Bound :=
  { action := mutationAction, program := programView, inputs := [], writes := cellNodes }

private def failsAt (payloadBody : List Nat) (code : Nat) : Bool :=
  match (planForBody payloadBody request).outcome with
  | .failed observed => observed == code && (planForBody payloadBody request).drafts.isEmpty
  | _ => false

def falseRow75 : RowCertificate :=
  { row75 with cell3 := { row75.cell3 with target := row75.cell3.listed } }

def falseRows : List RowCertificate := rows.set 3 falseRow75
def falseBody : List Nat := falseRows.flatMap encodeRow

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard decodeRows? falseBody == some falseRows
#guard firstFailure? falseRows == some 603
#guard !validRows falseRows
#guard !factFormat.validateBody falseBody
#guard failsAt falseBody 603

def wrongRow80 : RowCertificate :=
  { row80 with cell2 :=
      { row80.cell2 with coordinate := { row := 80, column := 3 } } }

def wrongCoordinateRows : List RowCertificate := rows.set 4 wrongRow80
def wrongCoordinateBody : List Nat := wrongCoordinateRows.flatMap encodeRow

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard firstFailure? wrongCoordinateRows == some 643
#guard !validRows wrongCoordinateRows
#guard failsAt wrongCoordinateBody 643

def swappedRows : List RowCertificate := [row60, row65, row75, row70, row80, row85]
def swappedBody : List Nat := swappedRows.flatMap encodeRow

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard firstFailure? swappedRows == none
#guard !validRows swappedRows
#guard failsAt swappedBody 1

private def action : Action := mutationAction

private def context (target : NodeId) (fact : Bound) :
    RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node := target, fact } }

#guard
  (batchFactSchema.replay checkerInput action
    (context (node 0) (.upper row60.cell1)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 29) (.upper row85.cell5)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 28) (.upper row85.cell5)) ()).isNone

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard trace?.any fun trace =>
  trace.program == program && trace.events.length == 30 &&
    trace.events.all fun event =>
      match event with
      | .rule step =>
          step.entry.replayKey == batchFactSchema.key &&
            step.event.programVersion == 0 && step.event.version == 1 &&
            step.assumptions.isEmpty && step.previous == .all && step.entry.body == body
      | _ => false

def baseFacts : List (NodeFact Bound) :=
  (List.range 31).map fun index => { node := node index, fact := .all }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_map] at member
  obtain ⟨index, within, rfl⟩ := member
  have indexWithin : index < 31 := List.mem_range.mp within
  have programSize : program.nodes.size = 31 := by decide
  simpa [node, programSize] using indexWithin

theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

private def decimalExpr (value : Decimal) : Expr :=
  mkApp2 (mkConst ``PntTable10Shard.Decimal.mk) (mkNatLit value.mantissa)
    (mkNatLit value.scale)

private def coordinateExpr (coordinate : Coordinate) : Expr :=
  mkApp2 (mkConst ``PntTable10Shard.Coordinate.mk) (mkNatLit coordinate.row)
    (mkNatLit coordinate.column)

private def cellExpr (cell : Cell) : Expr :=
  mkApp3 (mkConst ``PntTable10Shard.Cell.mk) (coordinateExpr cell.coordinate)
    (decimalExpr cell.listed) (decimalExpr cell.target)

private def boundExpr : Bound → Expr
  | .all => mkConst ``PntTable10Shard.Bound.all
  | .upper cell => mkApp (mkConst ``PntTable10Shard.Bound.upper) (cellExpr cell)
  | .empty => mkConst ``PntTable10Shard.Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``PntTable10Shard.Bound) (fun fact => pure (boundExpr fact))

private def seedAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence (semantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def frontendContext : ProofFrontend.Context Bound Name :=
  { encoder := boundEncoder
    resolveSchema := pure
    semantics := mkConst ``semantics
    domain := mkConst ``boundSchema
    laws := mkConst ``laws
    stableLaw := mkConst ``stableLaw
    input := mkConst ``checkerInput
    assumed := ``seedAssumed
    baseFacts
    baseFactsTerm := mkConst ``baseFacts
    baseProgram := program
    baseProgramTerm := mkConst ``program
    basePrefix := mkConst ``basePrefix
    baseWithin := mkConst ``baseWithin
    initialExtension := mkConst ``initialExtension
    finalPrefix := mkConst ``basePrefix
    sameOperations := mkConst ``sameOperations
    top := boundSchema.top }

private meta def emitState : MetaM (ProofFrontend.State Bound) := do
  let some fixture := fixture?
    | throwError "pnt_table10_convex: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_table10_convex: chronology quotation failed"
  unless trace.program == program && trace.events.length == 30 do
    throwError "pnt_table10_convex: expected the exact thirty-coordinate chronology"
  ProofFrontend.emitTrace frontendContext trace.program trace.events fixture.registry.emit

private meta def emitEvidence (target : NodeId) (fact : Bound) : MetaM Expr := do
  let state ← emitState
  ProofFrontend.closeTarget frontendContext state
    { node := target, version := 1 } fact { node := target, fact }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option exponentiation.threshold 2000 in
noncomputable def replayLast : Evidence
    (semantics.Entails program baseFacts { node := node 29, fact := .upper row85.cell5 }) := by
  run_tac
    let evidence ← emitEvidence (node 29) (.upper row85.cell5)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table10_convex: evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option exponentiation.threshold 2000 in
/-- The generic proof frontend closes every installed coordinate fact. -/
theorem replayEveryCell : True := by
  run_tac
    let state ← emitState
    for (cell, index) in cells.zipIdx do
      let _ ← ProofFrontend.closeTarget frontendContext state
        { node := node index, version := 1 } (.upper cell)
        { node := node index, fact := .upper cell }
    let goal ← getMainGoal
    goal.assign (mkConst ``True.intro)
    replaceMainGoal []

/-- Exact tuple-membership and finite-column source shape for every row in
the six-row batch, after PNT+'s localized `B_8_exact` majorant rewrite. -/
theorem table_10_rows_60_85_dispatch (value : RowCertificate) (rowMember : value ∈ rows)
    (B : Nat → ℝ)
    (member : ((value.row : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, ∀ y ∈ Set.Icc (value.row : ℝ) value.nextRow,
      majorant value k y ≤ B k * PntTable10Shard.margin.value :=
  rowOfMem value rowMember B member

/--
info: 'Hex.IntervalMathlib.PntTable10ConvexConformance.table_10_rows_60_85_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table_10_rows_60_85_dispatch

/--
info: 'Hex.IntervalMathlib.PntTable10ConvexConformance.replayLast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms replayLast

end Hex.IntervalMathlib.PntTable10ConvexConformance
