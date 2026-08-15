/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable10LargePointwise
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# PNT+ Table 10 large-decimal pointwise-row conformance

One bounded action authenticates all five coordinates of row `13800.7464`.
Endpoint and coordinate mutations reject without a draft or retry.
-/

namespace Hex.IntervalMathlib.PntTable10LargePointwiseConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntTable10LargePointwise

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
    target := { node := node 4, fact := .upper certificate.cell5 } }

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
#guard validCertificate certificate
#guard cells.length == 5
#guard body.length == 41
#guard decodeCertificate? body == some certificate
#guard decodeBatch? body == some ()
#guard expectedCandidates.length == 5
#guard certificate.row == PntTable10Shard.decimal 138007464 4
#guard certificate.nextRow == 14000
#guard certificate.a2 == PntTable10Shard.decimal 19913 0
#guard certificate.epsilon == PntTable10Shard.decimal 25423 39
#guard certificate.tail == PntTable10Shard.decimal 1 100
#guard certificate.cell1.listed == PntTable10Shard.decimal 35592 35
#guard certificate.cell5.listed == PntTable10Shard.decimal 13673 18
#guard run?.isSome
#guard fixture?.isSome
#guard fixture?.any fun fixture => fixture.session.state.engine.chronology.size == 5
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.requests == 1
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.candidates == 5
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.improvements == 5
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
    generations := Array.replicate 6 0
    depths := (Array.replicate 5 0).push 1 }

private def request : RuleRequest Bound :=
  { action := mutationAction, program := programView, inputs := [], writes := cellNodes }

private def failsAt (payloadBody : List Nat) (code : Nat) : Bool :=
  match (planForBody payloadBody request).outcome with
  | .failed observed => observed == code && (planForBody payloadBody request).drafts.isEmpty
  | _ => false

def falseCertificate : RowCertificate :=
  { certificate with cell1 := { certificate.cell1 with target := certificate.cell1.listed } }

def falseBody : List Nat := encodeCertificate falseCertificate

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard decodeCertificate? falseBody == some falseCertificate
#guard firstFailure? falseCertificate == some 801
#guard !validCertificate falseCertificate
#guard !factFormat.validateBody falseBody
#guard failsAt falseBody 801

def wrongCoordinate : RowCertificate :=
  { certificate with cell3 :=
      { certificate.cell3 with coordinate := { row := rowCode, column := 4 } } }

def wrongCoordinateBody : List Nat := encodeCertificate wrongCoordinate

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard firstFailure? wrongCoordinate == some 804
#guard !validCertificate wrongCoordinate
#guard failsAt wrongCoordinateBody 804

def wrongRow : RowCertificate :=
  { certificate with cell2 :=
      { certificate.cell2 with coordinate := { row := rowCode + 1, column := 2 } } }

def wrongRowBody : List Nat := encodeCertificate wrongRow

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard firstFailure? wrongRow == some 802
#guard !validCertificate wrongRow
#guard failsAt wrongRowBody 802

private def action : Action := mutationAction

private def context (target : NodeId) (fact : Bound) :
    RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node := target, fact } }

#guard
  (batchFactSchema.replay checkerInput action
    (context (node 0) (.upper certificate.cell1)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 4) (.upper certificate.cell5)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 3) (.upper certificate.cell5)) ()).isNone

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard trace?.any fun trace =>
  trace.program == program && trace.events.length == 5 &&
    trace.events.all fun event =>
      match event with
      | .rule step =>
          step.entry.replayKey == batchFactSchema.key &&
            step.event.programVersion == 0 && step.event.version == 1 &&
            step.assumptions.isEmpty && step.previous == .all && step.entry.body == body
      | _ => false

def baseFacts : List (NodeFact Bound) :=
  (List.range 6).map fun index => { node := node index, fact := .all }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_map] at member
  obtain ⟨index, within, rfl⟩ := member
  have indexWithin : index < 6 := List.mem_range.mp within
  have programSize : program.nodes.size = 6 := by decide
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
    | throwError "pnt_table10_large: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_table10_large: chronology quotation failed"
  unless trace.program == program && trace.events.length == 5 do
    throwError "pnt_table10_large: expected the exact five-coordinate chronology"
  ProofFrontend.emitTrace frontendContext trace.program trace.events fixture.registry.emit

private meta def emitEvidence (target : NodeId) (fact : Bound) : MetaM Expr := do
  let state ← emitState
  ProofFrontend.closeTarget frontendContext state
    { node := target, version := 1 } fact { node := target, fact }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option exponentiation.threshold 2000 in
noncomputable def replayLast : Evidence
    (semantics.Entails program baseFacts { node := node 4, fact := .upper certificate.cell5 }) := by
  run_tac
    let evidence ← emitEvidence (node 4) (.upper certificate.cell5)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table10_large: evidence has the wrong theorem"
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

/-- Exact tuple-membership and finite-column source shape for row 13800.7464,
matching the numeric premise of PNT+ `row_bound_pointwise`. -/
theorem table_10_row13800_7464_dispatch (B : Nat → ℝ)
    (member : (certificate.row.value, B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, premise certificate k ≤ B k * PntTable10Shard.margin.value :=
  rowOfMem B member

set_option exponentiation.threshold 2000 in
/-- The rational majorant exceeds the uncorrected first source target, so the
bounded provider rejects the mutation without a retry. -/
theorem rejectBareCertificate :
    ¬ (endpoint certificate certificate.cell1).value ≤ certificate.cell1.listed.value := by
  norm_num [endpoint, certificate, sourceCell, PntTable10Shard.Decimal.powNat,
    PntTable10Shard.Decimal.value, PntTable10Shard.Decimal.mul,
    PntTable10Shard.Decimal.add, PntTable10Shard.corrected,
    PntTable10Shard.margin, PntTable10Shard.decimal]

/--
info: 'Hex.IntervalMathlib.PntTable10LargePointwiseConformance.table_10_row13800_7464_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table_10_row13800_7464_dispatch

/--
info: 'Hex.IntervalMathlib.PntTable10LargePointwiseConformance.replayLast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms replayLast

/--
info: 'Hex.IntervalMathlib.PntTable10LargePointwiseConformance.rejectBareCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rejectBareCertificate

end Hex.IntervalMathlib.PntTable10LargePointwiseConformance
