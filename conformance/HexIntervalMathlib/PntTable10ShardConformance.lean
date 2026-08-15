/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable10Shard
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# PNT+ Table 10 row-25 shard conformance

This canary authenticates and replays all five coordinates of pinned Table 10
row 25 as one batch.  The historically bare `k = 5` endpoint is also decoded
as a mutation and rejected at its coordinate, with a separate kernel proof
that the un-margined endpoint inequality is false.
-/

namespace Hex.IntervalMathlib.PntTable10ShardConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntTable10Shard

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
  some (TargetRun.drive factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name

def fixture? : Option Fixture := do
  let result ← run?
  let .target _ := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages | none
  some { session := result.session, registry }

#guard certificate.row == 25
#guard certificate.nextRow == 26
#guard certificate.cells.length == 5
#guard certificate.cell5.coordinate == { row := 25, column := 5 }
#guard certificate.cell5.listed == decimal 71291 3
#guard certificate.cell5.target == corrected (decimal 71291 3)
#guard body.length == 46
#guard decodeCertificate? body == some certificate
#guard decodeBatch? body == some ()
#guard validCertificate certificate
#guard expectedCandidates.length == 5
#guard run?.isSome
#guard fixture?.isSome
#guard fixture?.any fun fixture => fixture.session.state.engine.chronology.size == 5
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.requests == 1
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.candidates == 5
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.improvements == 5
#guard fixture?.any fun fixture => fixture.session.arena.entries.size == 1
#guard fixture?.any fun fixture =>
  fixture.registry.emit.find? batchFactSchema.key == some ``batchFactSchema

def bareK5 : Cell := { certificate.cell5 with target := certificate.cell5.listed }
def falseCertificate : Certificate := { certificate with cell5 := bareK5 }
def falseBody : List Nat := certificateBody falseCertificate

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
    depths := #[0, 0, 0, 0, 0, 1] }

private def request : RuleRequest Bound :=
  { action := mutationAction, program := programView, inputs := [], writes := cellNodes }

private def failsAt (cells : List Nat) (code : Nat) : Bool :=
  match (planForBody cells request).outcome with
  | .failed observed => observed == code && (planForBody cells request).drafts.isEmpty
  | _ => false

/- The mutation is structurally decodable, but its exact row-25/k=5 endpoint
check fails.  Planning reports coordinate `25 * 8 + 5 = 205`, retains no
draft, and does not request a precision retry. -/
#guard decodeCertificate? falseBody == some falseCertificate
#guard firstFailure? falseCertificate == some 205
#guard !validCertificate falseCertificate
#guard !factFormat.validateBody falseBody
#guard failsAt falseBody 205

def wrongCoordinate : Certificate :=
  { certificate with cell3 := { certificate.cell3 with coordinate := { row := 25, column := 4 } } }
#guard decodeCertificate? (certificateBody wrongCoordinate) == some wrongCoordinate
#guard firstFailure? wrongCoordinate == some 204
#guard !validCertificate wrongCoordinate
#guard failsAt (certificateBody wrongCoordinate) 204

private def action : Action :=
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
  | some fixture =>
      Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard trace?.any fun trace =>
  trace.program == program && trace.events.length == 5 &&
    trace.events.all fun event =>
      match event with
      | .rule step =>
          step.entry.replayKey == batchFactSchema.key &&
            step.event.programVersion == 0 && step.event.version == 1 &&
            step.assumptions.isEmpty && step.previous == .all &&
            step.entry.body == body
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
  mkApp2 (mkConst ``Decimal.mk) (mkNatLit value.mantissa) (mkNatLit value.scale)

private def coordinateExpr (coordinate : Coordinate) : Expr :=
  mkApp2 (mkConst ``Coordinate.mk) (mkNatLit coordinate.row)
    (mkNatLit coordinate.column)

private def cellExpr (cell : Cell) : Expr :=
  mkApp3 (mkConst ``Cell.mk) (coordinateExpr cell.coordinate)
    (decimalExpr cell.listed) (decimalExpr cell.target)

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .upper cell => mkApp (mkConst ``Bound.upper) (cellExpr cell)
  | .empty => mkConst ``Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))

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
    | throwError "pnt_table10_shard: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_table10_shard: chronology quotation failed"
  unless trace.program == program && trace.events.length == 5 do
    throwError "pnt_table10_shard: expected the exact five-coordinate chronology"
  ProofFrontend.emitTrace frontendContext trace.program trace.events fixture.registry.emit

private meta def emitEvidence (target : NodeId) (fact : Bound) : MetaM Expr := do
  let state ← emitState
  ProofFrontend.closeTarget frontendContext state
    { node := target, version := 1 } fact { node := target, fact }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
noncomputable def replayK5 : Evidence
    (semantics.Entails program baseFacts
      { node := node 4, fact := .upper certificate.cell5 }) := by
  run_tac
    let evidence ← emitEvidence (node 4) (.upper certificate.cell5)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table10_shard: k=5 evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The generic proof frontend folds the checked shared-row chronology. -/
theorem replayEveryCell : True := by
  run_tac
    let state ← emitState
    for (cell, index) in certificate.cells.zipIdx do
      let target := node index
      let fact := Bound.upper cell
      let _ ← ProofFrontend.closeTarget frontendContext state
        { node := target, version := 1 } fact { node := target, fact }
    let goal ← getMainGoal
    goal.assign (mkConst ``True.intro)
    replaceMainGoal []

/-- Source-shaped numeric bridge for the corrected row-25/k=5 cell.  PNT+ can
rewrite its local coefficient majorant to this theorem without retaining a
LeanCert tactic call. -/
theorem table_10_row25_k5_margin :
    ∀ y ∈ Set.Icc (25 : ℝ) 26,
      majorant 5 y ≤ certificate.cell5.target.value :=
  row25Cell certificate.cell5 (by simp [Certificate.cells])

/-- The checked coordinate batch supplies all five corrected row-25 cells. -/
theorem table_10_row25_margin (cell : Cell) (member : cell ∈ certificate.cells) :
    RowHolds cell := row25Cell cell member

/-- The exact tuple-membership and finite-column source-dispatch shape, after
the localized rewrite from `B_8_exact` to its checked numeric majorant. -/
theorem table_10_row25_dispatch (B : Nat → ℝ)
    (member : ((25 : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, ∀ y ∈ Set.Icc (25 : ℝ) 26,
      majorant k y ≤ B k * margin.value :=
  row25OfMem B member

/--
info: 'Hex.IntervalMathlib.PntTable10ShardConformance.table_10_row25_k5_margin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table_10_row25_k5_margin

/--
info: 'Hex.IntervalMathlib.PntTable10ShardConformance.table_10_row25_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table_10_row25_dispatch

/--
info: 'Hex.IntervalMathlib.PntTable10ShardConformance.replayK5' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms replayK5

/--
info: 'Hex.Interval.Experiment.PntTable10Shard.rejectBareK5' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rejectBareK5

end Hex.IntervalMathlib.PntTable10ShardConformance
