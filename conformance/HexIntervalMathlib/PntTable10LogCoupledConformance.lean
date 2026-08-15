/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable10Exact
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# PNT+ Table 10 logarithmic-transition conformance

One bounded action authenticates the consecutive rows `43` and
`19 * Real.log 10`.  Shared endpoint, coordinate, chronology, and false-target
mutations all reject without producing a draft or retry.
-/

namespace Hex.IntervalMathlib.PntTable10LogCoupledConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntTable10LogCoupled

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
    target := { node := node 9, fact := .upper certificate.rowLog.cell5 } }

private def run? : Option (TargetRun.Result Bound Unit) := do
  let .ok session := start | none
  some (TargetRun.drive PntTable10Shard.factDomain checkerInput.target.node
    checkerInput.target.fact firstOffer limits.policy.maxDecisions session ())

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
#guard (cells certificate).length == 10
#guard body.length == 86
#guard decodeCertificate? body == some certificate
#guard decodeBatch? body == some ()
#guard expectedCandidates.length == 10
#guard certificate.row43.rowCode == 43
#guard certificate.rowLog.rowCode == logRowCode
#guard certificate.logUpper == PntTable10Shard.decimal 4375 2
#guard certificate.halfTail == PntTable10Shard.decimal 317 12
#guard certificate.twoThirdTail == PntTable10Shard.decimal 216 15
#guard certificate.row43K5 == PntTable10Shard.decimal 31563 4
#guard checkBare certificate
#guard certificate.row43.cell1.listed == PntTable10Shard.decimal 85986 11
#guard certificate.rowLog.cell5.listed == PntTable10Shard.decimal 32352 4
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

private def failsWithoutDraft (value : Certificate) : Bool :=
  match (planForBody (encodeCertificate value) request).outcome with
  | .failed _ => (planForBody (encodeCertificate value) request).drafts.isEmpty
  | _ => false

def falseCertificate : Certificate :=
  { certificate with row43 :=
      { certificate.row43 with cell1 :=
          { certificate.row43.cell1 with target := certificate.row43.cell1.listed } } }

def falseBody : List Nat := encodeCertificate falseCertificate

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard decodeCertificate? falseBody == some falseCertificate
#guard firstFailure? falseCertificate == some 345
#guard !validCertificate falseCertificate
#guard !factFormat.validateBody falseBody
#guard failsAt falseBody 345

def wrongCoordinate : Certificate :=
  { certificate with rowLog :=
      { certificate.rowLog with cell3 :=
          { certificate.rowLog.cell3 with coordinate := { row := 43, column := 3 } } } }

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard !validCertificate wrongCoordinate
#guard failsAt (encodeCertificate wrongCoordinate) 347

def crossedRows : Certificate :=
  { certificate with row43 := certificate.rowLog, rowLog := certificate.row43 }

#guard decodeCertificate? (encodeCertificate crossedRows) == some crossedRows
#guard firstFailure? crossedRows ==
  some (PntTable10Shard.coordinateCode (bareCell crossedRows).coordinate)
#guard !validCertificate crossedRows
#guard failsAt (encodeCertificate crossedRows)
  (PntTable10Shard.coordinateCode (bareCell crossedRows).coordinate)

def wrongHalfBase : Certificate :=
  { certificate with halfBase := PntTable10Shard.decimal 606530661 9 }

def wrongTwoThirdBase : Certificate :=
  { certificate with twoThirdBase := PntTable10Shard.decimal 513417121 9 }

def wrongLogUpper : Certificate :=
  { certificate with logUpper := PntTable10Shard.decimal 44 0 }

def wrongHalfTail : Certificate :=
  { certificate with halfTail := PntTable10Shard.decimal 318 12 }

def wrongTwoThirdTail : Certificate :=
  { certificate with twoThirdTail := PntTable10Shard.decimal 217 15 }

/-- A target below the authenticated rational endpoint is rejected before any
draft survives. -/
def wrongBareTarget : Certificate :=
  { certificate with row43K5 := PntTable10Shard.decimal 31505 4 }

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 2000 in
#guard failsWithoutDraft wrongHalfBase
#guard failsWithoutDraft wrongTwoThirdBase
#guard failsWithoutDraft wrongLogUpper
#guard failsWithoutDraft wrongHalfTail
#guard failsWithoutDraft wrongTwoThirdTail
#guard !checkBare wrongBareTarget
#guard firstFailure? wrongBareTarget == some 349
#guard failsAt (encodeCertificate wrongBareTarget) 349

private def action : Action := mutationAction

private def context (target : NodeId) (fact : Bound) :
    RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node := target, fact } }

#guard
  (batchFactSchema.replay checkerInput action
    (context (node 0) (.upper certificate.row43.cell1)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 9) (.upper certificate.rowLog.cell5)) ()).isSome
#guard
  (batchFactSchema.replay checkerInput action
    (context (node 8) (.upper certificate.rowLog.cell5)) ()).isNone

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
    | throwError "pnt_table10_log: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_table10_log: chronology quotation failed"
  unless trace.program == program && trace.events.length == 10 do
    throwError "pnt_table10_log: expected the exact ten-coordinate chronology"
  ProofFrontend.emitTrace frontendContext trace.program trace.events fixture.registry.emit

private meta def emitEvidence (target : NodeId) (fact : Bound) : MetaM Expr := do
  let state ← emitState
  ProofFrontend.closeTarget frontendContext state
    { node := target, version := 1 } fact { node := target, fact }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option exponentiation.threshold 2000 in
noncomputable def replayLast : Evidence
    (semantics.Entails program baseFacts
      { node := node 9, fact := .upper certificate.rowLog.cell5 }) := by
  run_tac
    let evidence ← emitEvidence (node 9) (.upper certificate.rowLog.cell5)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table10_log: evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option exponentiation.threshold 2000 in
/-- The generic proof frontend closes every installed coordinate premise. -/
theorem replayEveryCell : True := by
  run_tac
    let state ← emitState
    for (cell, index) in (cells certificate).zipIdx do
      let _ ← ProofFrontend.closeTarget frontendContext state
        { node := node index, version := 1 } (.upper cell)
        { node := node index, fact := .upper cell }
    let goal ← getMainGoal
    goal.assign (mkConst ``True.intro)
    replaceMainGoal []

/-- Exact tuple-membership and finite-column source shape for pinned row 43. -/
theorem table_10_row43_dispatch (B : Nat → ℝ)
    (member : ((43 : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, ∀ y ∈ Set.Icc (43 : ℝ) (19 * Real.log 10),
      majorant row43 k y ≤ B k * PntTable10Shard.margin.value := by
  simpa [certificate, lowerPoint, upperPoint, row43, rowCertificate] using
    rowOfMem row43 (by simp [rows, certificate]) B member

/-- Exact tuple-membership and finite-column source shape for the consecutive
pinned row `19 * log 10`. -/
theorem table_10_row19log10_dispatch (B : Nat → ℝ)
    (member : (19 * Real.log 10, B 1, B 2, B 3, B 4, B 5) ∈ sourceTable) :
    ∀ k ∈ Finset.Icc 1 5, ∀ y ∈ Set.Icc (19 * Real.log 10) 44,
      majorant rowLog k y ≤ B k * PntTable10Shard.margin.value := by
  simpa [certificate, lowerPoint, upperPoint, rowLog, rowCertificate, logRowCode] using
    rowOfMem rowLog (by simp [rows, certificate]) B member

/-- Exact source-shaped replacement for `table_10_row43_k5`; unlike the
margin dispatcher, this retains the source theorem's tighter `3.1563`
endpoint. -/
theorem table_10_row43_k5 (a1 a2 epsilon : ℝ)
    (ha1 : a1 ≤ row43.a1.value) (ha2 : a2 ≤ row43.a2.value)
    (hepsilon : epsilon ≤ row43.epsilon.value) :
    PntTable10Exact.exactBound 5 a1 a2 epsilon 43 (19 * Real.log 10) ≤
      (3.1563 : ℝ) := by
  convert PntTable10Exact.LogCoupled.row43K5 a1 a2 epsilon
      (by norm_num [row43, rowCertificate, PntTable10Shard.Decimal.value,
        PntTable10Shard.decimal])
      (by norm_num [row43, rowCertificate, PntTable10Shard.Decimal.value,
        PntTable10Shard.decimal])
      (by norm_num [row43, rowCertificate, PntTable10Shard.Decimal.value,
        PntTable10Shard.decimal])
      ha1 ha2 hepsilon using 1;
    norm_num [certificate, PntTable10Shard.Decimal.value, PntTable10Shard.decimal]

set_option exponentiation.threshold 2000 in
/-- The row-43 rational majorant exceeds its uncorrected first source target,
so the bounded provider rejects that false coordinate without retry. -/
theorem rejectBareRow43 :
    ¬ (rightEndpoint certificate certificate.row43 certificate.row43.cell1).value ≤
      certificate.row43.cell1.listed.value := by
  norm_num [rightEndpoint, logEndpoint, certificate, row43, rowLog, rowCertificate,
    sourceCell, decimalPow, PntTable10Shard.Decimal.value, PntTable10Shard.Decimal.mul,
    PntTable10Shard.Decimal.add, PntTable10Shard.decimal]

/--
info: 'Hex.IntervalMathlib.PntTable10LogCoupledConformance.table_10_row43_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table_10_row43_dispatch

/--
info: 'Hex.IntervalMathlib.PntTable10LogCoupledConformance.table_10_row19log10_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table_10_row19log10_dispatch

/--
info: 'Hex.IntervalMathlib.PntTable10LogCoupledConformance.table_10_row43_k5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms table_10_row43_k5

/--
info: 'Hex.IntervalMathlib.PntTable10LogCoupledConformance.replayLast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms replayLast

/--
info: 'Hex.IntervalMathlib.PntTable10LogCoupledConformance.rejectBareRow43' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rejectBareRow43

end Hex.IntervalMathlib.PntTable10LogCoupledConformance
