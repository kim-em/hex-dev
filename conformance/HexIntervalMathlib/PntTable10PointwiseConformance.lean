/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable10Pointwise
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# PNT+ Table 10 pointwise-row batch conformance

One bounded action authenticates rows 90 and 95 and installs all ten numeric
premises. Endpoint, coordinate, and row-order mutations are rejected without
a draft or precision retry.
-/

namespace Hex.IntervalMathlib.PntTable10PointwiseConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntTable10Pointwise

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
    target := { node := node 9, fact := .upper row95.cell5 } }

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
#guard rows.length == 2
#guard cells.length == 10
#guard body.length == 76
#guard decodeRows? body == some rows
#guard decodeBatch? body == some ()
#guard expectedCandidates.length == 10
#guard row90.row == 90 && row90.nextRow == 95
#guard row95.row == 95 && row95.nextRow == 100
#guard row90.a1 == PntTable10Shard.decimal 2 0
#guard row90.a2 == PntTable10Shard.decimal 132 0
#guard row90.epsilon == PntTable10Shard.decimal 25214 16
#guard row90.cell1.listed == PntTable10Shard.decimal 23952 14
#guard row95.cell5.listed == PntTable10Shard.decimal 24919 6
#guard run?.isSome
#guard fixture?.isSome
#guard fixture?.any fun fixture => fixture.session.state.engine.chronology.size == 10
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.requests == 1
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.candidates == 10
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.improvements == 10
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
    generations := Array.replicate 11 0
    depths := (Array.replicate 10 0).push 1 }

private def request : RuleRequest Bound :=
  { action := mutationAction, program := programView, inputs := [], writes := cellNodes }

private def failsAt (payloadBody : List Nat) (code : Nat) : Bool :=
  match (planForBody payloadBody request).outcome with
  | .failed observed => observed == code && (planForBody payloadBody request).drafts.isEmpty
  | _ => false

def falseRow90 : RowCertificate :=
  { row90 with cell1 := { row90.cell1 with target := row90.cell1.listed } }

def falseRows : List RowCertificate := [falseRow90, row95]
def falseBody : List Nat := falseRows.flatMap encodeRow

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard decodeRows? falseBody == some falseRows
#guard firstFailure? falseRows == some 721
#guard !validRows falseRows
#guard !factFormat.validateBody falseBody
#guard failsAt falseBody 721

def wrongRow95 : RowCertificate :=
  { row95 with cell3 :=
      { row95.cell3 with coordinate := { row := 95, column := 4 } } }

def wrongCoordinateRows : List RowCertificate := [row90, wrongRow95]
def wrongCoordinateBody : List Nat := wrongCoordinateRows.flatMap encodeRow

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard firstFailure? wrongCoordinateRows == some 764
#guard !validRows wrongCoordinateRows
#guard failsAt wrongCoordinateBody 764

def swappedRows : List RowCertificate := [row95, row90]
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
    (context (node 0) (.upper row90.cell1)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 9) (.upper row95.cell5)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 8) (.upper row95.cell5)) ()).isNone

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard trace?.any fun trace =>
  trace.program == program && trace.events.length == 10 &&
    trace.events.all fun event =>
      match event with
      | .rule step =>
          step.entry.replayKey == batchFactSchema.key &&
            step.event.programVersion == 0 && step.event.version == 1 &&
            step.assumptions.isEmpty && step.previous == .all && step.entry.body == body
      | _ => false

def baseFacts : List (NodeFact Bound) :=
  (List.range 11).map fun index => { node := node index, fact := .all }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_map] at member
  obtain ⟨index, within, rfl⟩ := member
  have indexWithin : index < 11 := List.mem_range.mp within
  have programSize : program.nodes.size = 11 := by decide
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
    | throwError "pnt_table10_pointwise: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_table10_pointwise: chronology quotation failed"
  unless trace.program == program && trace.events.length == 10 do
    throwError "pnt_table10_pointwise: expected the exact ten-coordinate chronology"
  ProofFrontend.emitTrace frontendContext trace.program trace.events fixture.registry.emit

private meta def emitEvidence (target : NodeId) (fact : Bound) : MetaM Expr := do
  let state ← emitState
  ProofFrontend.closeTarget frontendContext state
    { node := target, version := 1 } fact { node := target, fact }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option exponentiation.threshold 2000 in
noncomputable def replayLast : Evidence
    (semantics.Entails program baseFacts { node := node 9, fact := .upper row95.cell5 }) := by
  run_tac
    let evidence ← emitEvidence (node 9) (.upper row95.cell5)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table10_pointwise: evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option exponentiation.threshold 2000 in
/-- The generic proof frontend closes every installed pointwise premise. -/
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

/-- Exact tuple-membership and finite-column source shape for rows 90 and 95,
matching the numeric premise of PNT+ `row_bound_pointwise`. -/
theorem table_10_rows_90_95_dispatch (value : RowCertificate) (rowMember : value ∈ rows)
    (B : Nat → ℝ)
    (member : ((value.row : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, premise value k ≤ B k * PntTable10Shard.margin.value :=
  rowOfMem value rowMember B member

set_option exponentiation.threshold 2000 in
/-- The authenticated rational majorant exceeds the uncorrected row-90/k=1
target, so the bounded provider rejects it without a retry or draft. -/
theorem rejectBareCertificate :
    ¬ (endpoint row90 row90.cell1).value ≤ row90.cell1.listed.value := by
  norm_num [endpoint, row90, rowCertificate, sourceCell, halfBase, twoThirdBase, decimalPow,
    PntTable10Shard.Decimal.powNat, PntTable10Shard.Decimal.value,
    PntTable10Shard.Decimal.mul, PntTable10Shard.Decimal.add,
    PntTable10Shard.corrected, PntTable10Shard.margin, PntTable10Shard.decimal]

/--
info: 'Hex.IntervalMathlib.PntTable10PointwiseConformance.table_10_rows_90_95_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table_10_rows_90_95_dispatch

/--
info: 'Hex.IntervalMathlib.PntTable10PointwiseConformance.replayLast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms replayLast

/--
info: 'Hex.IntervalMathlib.PntTable10PointwiseConformance.rejectBareCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rejectBareCertificate

end Hex.IntervalMathlib.PntTable10PointwiseConformance
