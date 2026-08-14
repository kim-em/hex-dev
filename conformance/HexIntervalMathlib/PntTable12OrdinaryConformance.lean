/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable12Ordinary
import HexIntervalMathlib.Experiment.PntTable12
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# PNT+ ordinary Table 12 generated-batch conformance

This file runs and replays the 115 cells not covered by the retained row-25
fixture.  Together they account for all 120 ordinary numerical leaves; the ten
logarithmic-row leaves remain separate acceptance work.
-/

namespace Hex.IntervalMathlib.PntTable12OrdinaryConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntTable12Ordinary

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts
    target := { node := node 114, fact := .upper finalCell } }

private def run? : Option (TargetRun.Result Bound Unit) := do
  let .ok session := start | none
  some (TargetRun.drive factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name
  reached : TargetRun.Reached Bound
  events : Array (TargetRun.Event Bound)

def fixture? : Option Fixture := do
  let result ← run?
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages | none
  some { session := result.session, registry, reached, events := result.events }

#guard ordinaryRows.length == 23
#guard ordinaryCells.length == 115
#guard cellNodes.length == 115
#guard batchBody.length == 391
#guard expectedCandidates.length == 115
#guard coordinateForNode? (node 0) == some { row := 20, column := 1 }
#guard coordinateForNode? (node 114) == some { row := 43, column := 5 }
#guard coordinateCode { row := 43, column := 5 } == 349

#guard run?.isSome
#guard fixture?.isSome
#guard fixture?.any fun fixture => fixture.events.size == 1
#guard fixture?.any fun fixture => fixture.session.state.engine.chronology.size == 115
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.requests == 1
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.replies == 1
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.candidates == 115
#guard fixture?.any fun fixture => fixture.session.state.engine.metrics.improvements == 115
#guard fixture?.any fun fixture => fixture.session.arena.entries.size == 1
#guard fixture?.any fun fixture =>
  fixture.registry.emit.find? batchFactSchema.key == some ``batchFactSchema

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := batchRuleKey
    node := node 115
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

#guard decodeBatch? batchBody == some ()
#guard decodeBatch? (batchBody ++ [0]) == none
#guard factFormat.validateBody batchBody
private def firstCell : CellCertificate :=
  { coordinate := { row := 20, column := 1 }, cut := decimal 168440 8 }
private def middleCell : CellCertificate :=
  { coordinate := { row := 32, column := 3 }, cut := decimal 7173770 9 }
#guard Bound.meet (.upper firstCell) (.upper finalCell) == .upper firstCell
#guard Bound.meet (.upper finalCell) (.upper firstCell) == .upper firstCell
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 0) (.upper firstCell)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 114) (.upper finalCell)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 113) (.upper finalCell)) ()).isNone

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture =>
      Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program && trace.events.length == 115 &&
      trace.events.all fun event =>
        match event with
        | .rule step =>
            step.entry.replayKey == batchFactSchema.key &&
              step.event.programVersion == 0 && step.event.version == 1 &&
              step.assumptions.isEmpty && step.previous == .all &&
              step.entry.body == batchBody
        | _ => false

/-! ## One generic frontend fold closes every coordinate -/

def baseFacts : List (NodeFact Bound) :=
  (List.range 116).map fun index => { node := node index, fact := .all }

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_map] at member
  obtain ⟨index, within, rfl⟩ := member
  have indexWithin : index < 116 := List.mem_range.mp within
  have programSize : program.nodes.size = 116 := by decide
  simpa [node, programSize] using indexWithin

theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

private def coordinateExpr (coordinate : Coordinate) : Expr :=
  mkApp2 (mkConst ``Coordinate.mk) (mkNatLit coordinate.row)
    (mkNatLit coordinate.column)

private def decimalExpr (value : Decimal) : Expr :=
  mkApp2 (mkConst ``Decimal.mk) (mkNatLit value.mantissa) (mkNatLit value.scale)

private def cellExpr (cell : CellCertificate) : Expr :=
  mkApp2 (mkConst ``CellCertificate.mk) (coordinateExpr cell.coordinate)
    (decimalExpr cell.cut)

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .upper cell => mkApp (mkConst ``Bound.upper) (cellExpr cell)

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
    | throwError "pnt_table12_ordinary: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_table12_ordinary: chronology quotation failed"
  unless trace.program == program && trace.events.length == 115 do
    throwError "pnt_table12_ordinary: expected the exact 115-cell chronology"
  ProofFrontend.emitTrace frontendContext trace.program trace.events fixture.registry.emit

private meta def checkEveryCell : MetaM Unit := do
  let state ← emitState
  for (cell, index) in ordinaryCells.zipIdx do
    let target := node index
    let fact := Bound.upper cell
    let _ ← ProofFrontend.closeTarget frontendContext state
      { node := target, version := 1 } fact { node := target, fact }

private meta def emitEvidence (target : NodeId) (fact : Bound) : MetaM Expr := do
  let state ← emitState
  ProofFrontend.closeTarget frontendContext state
    { node := target, version := 1 } fact { node := target, fact }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
noncomputable def replayFirstCell : Evidence
    (semantics.Entails program baseFacts
      { node := node 0, fact := .upper firstCell }) := by
  run_tac
    let evidence ← emitEvidence (node 0) (.upper firstCell)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12_ordinary: first-cell evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
noncomputable def replayMiddleCell : Evidence
    (semantics.Entails program baseFacts
      { node := node 57, fact := .upper middleCell }) := by
  run_tac
    let evidence ← emitEvidence (node 57) (.upper middleCell)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12_ordinary: middle-cell evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
noncomputable def replayLastCell : Evidence
    (semantics.Entails program baseFacts
      { node := node 114, fact := .upper finalCell }) := by
  run_tac
    let evidence ← emitEvidence (node 114) (.upper finalCell)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12_ordinary: last-cell evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The generic frontend folds the one 115-event chronology and closes every
source coordinate from the uniform indexed schema. -/
theorem replayEveryOrdinaryCell : True := by
  run_tac
    checkEveryCell
    let goal ← getMainGoal
    goal.assign (mkConst ``True.intro)
    replaceMainGoal []


/-- All 23 generated row certificates satisfy their five exact source cuts. -/
theorem table12OrdinaryRows (certificate : RowCertificate)
    (member : certificate ∈ ordinaryRows) : RowHolds certificate :=
  ordinaryRowsBounds certificate member

/-- Combined package boundary: the retained row-25 theorem plus the generated
23-row table account for all 120 ordinary numerical leaves. -/
theorem table12AllOrdinary :
    PntTable12.row25Value 1 ≤ 175002 / 1000000000 ∧
      PntTable12.row25Value 2 ≤ 437505 / 100000000 ∧
      PntTable12.row25Value 3 ≤ 109377 / 1000000 ∧
      PntTable12.row25Value 4 ≤ 273441 / 100000 ∧
      PntTable12.row25Value 5 ≤ 683601 / 10000 ∧
      ∀ certificate ∈ ordinaryRows, RowHolds certificate := by
  exact ⟨PntTable12.row25Bounds.1, PntTable12.row25Bounds.2.1,
    PntTable12.row25Bounds.2.2.1, PntTable12.row25Bounds.2.2.2.1,
    PntTable12.row25Bounds.2.2.2.2, ordinaryRowsBounds⟩

/--
info: 'Hex.IntervalMathlib.PntTable12OrdinaryConformance.table12OrdinaryRows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table12OrdinaryRows

/--
info: 'Hex.Interval.Experiment.PntTable12Ordinary.ordinaryCertificatesMatchSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ordinaryCertificatesMatchSource

/--
info: 'Hex.IntervalMathlib.PntTable12OrdinaryConformance.replayFirstCell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms replayFirstCell

/--
info: 'Hex.IntervalMathlib.PntTable12OrdinaryConformance.replayMiddleCell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms replayMiddleCell

/--
info: 'Hex.IntervalMathlib.PntTable12OrdinaryConformance.replayLastCell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms replayLastCell

/--
info: 'Hex.IntervalMathlib.PntTable12OrdinaryConformance.table12AllOrdinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table12AllOrdinary

end Hex.IntervalMathlib.PntTable12OrdinaryConformance
