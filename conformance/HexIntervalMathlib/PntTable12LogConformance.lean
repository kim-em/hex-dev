/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable12Log
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# PNT+ Table 12 logarithmic-row conformance

Two checked logarithm windows feed two five-cell batch actions. This completes
the ten logarithmic leaves that follow the 120-cell ordinary fixture.
-/

namespace Hex.IntervalMathlib.PntTable12LogConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntTable12Log
open PntTable12Ordinary (Decimal)

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

def checkerInput : CheckerInput Bound :=
  { baseProgram := program
    initialFacts
    target := { node := node 13, fact := Bound.upper thirtyTwoRow.cell5 } }

private def run? (input : CheckerInput Bound) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain input.baseProgram
      packages input.initialFacts limits
    | none
  some (TargetRun.drive factDomain input.target.node input.target.fact
    firstOffer limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name
  reached : TargetRun.Reached Bound
  events : Array (TargetRun.Event Bound)

def fixture? : Option Fixture := do
  let result ← run? checkerInput
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { session := result.session, registry, reached, events := result.events }

#guard run? checkerInput |>.isSome
#guard (run? checkerInput).any fun result =>
  match result.stop with
  | .target _ => true
  | _ => false
#guard fixture?.isSome
#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 13, version := 1 } : SeenVersion) &&
      fixture.reached.fact == Bound.upper thirtyTwoRow.cell5 &&
      fixture.events.size == 4 &&
      fixture.session.state.engine.chronology.size == 12 &&
      fixture.session.state.engine.metrics.requests == 4 &&
      fixture.session.state.engine.metrics.replies == 4 &&
      fixture.session.state.engine.metrics.candidates == 12 &&
      fixture.session.state.engine.metrics.improvements == 12 &&
      fixture.session.arena.entries.size == 4

def trace? : Option (Frontend.Trace Bound) :=
  match fixture? with
  | none => none
  | some fixture =>
      Frontend.trace? fixture.session.state.engine fixture.session.arena

private def fiveWindowAssumptions : List (NodeFact Bound) :=
  [{ node := node 1, fact := Bound.window fiveRow.lower fiveRow.upper }]

private def thirtyTwoWindowAssumptions : List (NodeFact Bound) :=
  [{ node := node 3, fact := Bound.window thirtyTwoRow.lower thirtyTwoRow.upper }]

#guard
  trace?.any fun trace =>
    trace.program == program &&
      match trace.events with
      | [.rule fiveWindow, .rule thirtyTwoWindow,
          .rule five1, .rule five2, .rule five3, .rule five4, .rule five5,
          .rule thirtyTwo1, .rule thirtyTwo2, .rule thirtyTwo3,
          .rule thirtyTwo4, .rule thirtyTwo5] =>
          fiveWindow.entry.replayKey == windowFactSchema.key &&
            fiveWindow.entry.body == windowBody fiveRow &&
            fiveWindow.assumptions ==
              [{ node := node 0, fact := Bound.point fiveRow.input }] &&
            fiveWindow.event.node == node 1 &&
            fiveWindow.event.fact == Bound.window fiveRow.lower fiveRow.upper &&
          thirtyTwoWindow.entry.replayKey == windowFactSchema.key &&
            thirtyTwoWindow.entry.body == windowBody thirtyTwoRow &&
            thirtyTwoWindow.assumptions ==
              [{ node := node 2, fact := Bound.point thirtyTwoRow.input }] &&
            thirtyTwoWindow.event.node == node 3 &&
            thirtyTwoWindow.event.fact ==
              Bound.window thirtyTwoRow.lower thirtyTwoRow.upper &&
          ([five1, five2, five3, five4, five5].all fun step =>
            step.entry.replayKey == fiveFactSchema.key &&
              step.entry.body == rowBody fiveRow &&
              step.assumptions == fiveWindowAssumptions &&
              step.previous == .all) &&
          ([thirtyTwo1, thirtyTwo2, thirtyTwo3, thirtyTwo4, thirtyTwo5].all fun step =>
            step.entry.replayKey == thirtyTwoFactSchema.key &&
              step.entry.body == rowBody thirtyTwoRow &&
              step.assumptions == thirtyTwoWindowAssumptions &&
              step.previous == .all)
      | _ => false

/-! ## Coordinate-specific source mutation rejection -/

private def fiveAction : Action :=
  { serial := 2
    programVersion := 0
    application := { index := 2 }
    rule := { index := 1 }
    key := fiveRuleKey
    node := node 14
    kind := .forward
    effort := 0
    generation := 0
    inputs := [{ node := node 1, version := 1 }]
    writes := fiveCellNodes }

private def programView : ProgramView :=
  { programVersion := 0
    operations := program.operations
    nodes := program.nodes
    generations := Array.replicate 16 0
    depths := #[0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2] }

private def fiveInput : FactView Bound where
  node := node 1
  fact := Bound.window fiveRow.lower fiveRow.upper
  version := 1

private def fiveRequest : RuleRequest Bound :=
  { action := fiveAction
    program := programView
    inputs := [fiveInput]
    writes := fiveCellNodes }

#guard coordinateCode falseFiveCoordinate == 401
#guard mutationCoordinate? falseFiveBody == some falseFiveCoordinate
#guard decodeRow? falseFiveBody == none
#guard !factFormat.validateBody falseFiveBody
#guard
  match (rowPlanForBody fiveRow falseFiveBody fiveRequest).outcome with
  | .failed diagnostic =>
      diagnostic == coordinateCode falseFiveCoordinate && diagnostic == 401
  | _ => false
#guard (rowPlanForBody fiveRow falseFiveBody fiveRequest).drafts.isEmpty

/-! ## Generic proof emission closes both log rows -/

abbrev baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := Bound.point fiveRow.input },
    { node := node 1, fact := .all },
    { node := node 2, fact := Bound.point thirtyTwoRow.input },
    { node := node 3, fact := .all },
    { node := node 4, fact := .all }, { node := node 5, fact := .all },
    { node := node 6, fact := .all }, { node := node 7, fact := .all },
    { node := node 8, fact := .all }, { node := node 9, fact := .all },
    { node := node 10, fact := .all }, { node := node 11, fact := .all },
    { node := node 12, fact := .all }, { node := node 13, fact := .all },
    { node := node 14, fact := .all }, { node := node 15, fact := .all }]

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp [baseFacts, program, node] at member ⊢
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

private def decimalExpr (value : Decimal) : Expr :=
  mkApp2 (mkConst ``Decimal.mk) (mkNatLit value.mantissa) (mkNatLit value.scale)

private def optionDecimalExpr : Option Decimal → Expr
  | none => mkApp (mkConst ``Option.none [0]) (mkConst ``Decimal)
  | some value =>
      mkApp2 (mkConst ``Option.some [0]) (mkConst ``Decimal) (decimalExpr value)

private def rangeExpr (value : Range) : Expr :=
  mkApp2 (mkConst ``Range.mk) (optionDecimalExpr value.lower)
    (optionDecimalExpr value.upper)

private def rowInputExpr (row : Name) : Expr :=
  mkProj ``RowCertificate 2 (mkConst row)

private def boundExpr (fact : Bound) : Expr :=
  if fact == Bound.point fiveRow.input then
    mkApp (mkConst ``Bound.point) (rowInputExpr ``fiveRow)
  else if fact == Bound.point thirtyTwoRow.input then
    mkApp (mkConst ``Bound.point) (rowInputExpr ``thirtyTwoRow)
  else
    match fact with
    | .all => mkConst ``Bound.all
    | .range value => mkApp (mkConst ``Bound.range) (rangeExpr value)
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
    | throwError "pnt_table12_log: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_table12_log: chronology quotation failed"
  unless trace.program == program && trace.events.length == 12 do
    throwError "pnt_table12_log: expected the exact 12-fact chronology"
  ProofFrontend.emitTrace frontendContext trace.program trace.events fixture.registry.emit

private meta def emitEvidence (target : NodeId) (fact : Bound) : MetaM Expr := do
  let state ← emitState
  ProofFrontend.closeTarget frontendContext state
    { node := target, version := 1 } fact { node := target, fact }

private meta def checkEveryLogCell : MetaM Unit := do
  let state ← emitState
  for (cell, index) in logCells.zipIdx do
    let target := node (index + 4)
    let fact := Bound.upper cell.cut
    let _ ← ProofFrontend.closeTarget frontendContext state
      { node := target, version := 1 } fact { node := target, fact }

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
noncomputable def replayFirstLogCell : Evidence
    (semantics.Entails program baseFacts
      { node := node 4, fact := Bound.upper fiveRow.cell1 }) := by
  run_tac
    let evidence ← emitEvidence (node 4) (Bound.upper fiveRow.cell1)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12_log: first-cell evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
noncomputable def replayLastLogCell : Evidence
    (semantics.Entails program baseFacts
      { node := node 13, fact := Bound.upper thirtyTwoRow.cell5 }) := by
  run_tac
    let evidence ← emitEvidence (node 13) (Bound.upper thirtyTwoRow.cell5)
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12_log: last-cell evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The generic frontend folds the shared 12-event chronology and closes all
ten logarithmic-row coordinates. -/
theorem replayEveryLogCell : True := by
  run_tac
    checkEveryLogCell
    let goal ← getMainGoal
    goal.assign (mkConst ``True.intro)
    replaceMainGoal []

/-- Full PNT+ Table 12 boundary after all 130 checked numerical leaves. -/
theorem table12All (b cell1 cell2 cell3 cell4 cell5 c capital m : ℝ)
    (member : (b, cell1, cell2, cell3, cell4, cell5, c, capital, m) ∈ table12) :
    b ^ 1 * tableS b c capital ≤ cell1 ∧
      b ^ 2 * tableS b c capital ≤ cell2 ∧
      b ^ 3 * tableS b c capital ≤ cell3 ∧
      b ^ 4 * tableS b c capital ≤ cell4 ∧
      b ^ 5 * tableS b c capital ≤ cell5 :=
  table12Check _ _ _ _ _ _ _ _ _ member

/--
info: 'Hex.IntervalMathlib.PntTable12LogConformance.replayFirstLogCell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms replayFirstLogCell

/--
info: 'Hex.IntervalMathlib.PntTable12LogConformance.replayLastLogCell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms replayLastLogCell

/--
info: 'Hex.IntervalMathlib.PntTable12LogConformance.table12All' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms table12All

/--
info: 'Hex.Interval.Experiment.PntTable12Log.table12MatchesSource' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms table12MatchesSource

/--
info: 'Hex.Interval.Experiment.PntTable12Log.rejectFalseFiveCell' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rejectFalseFiveCell

end Hex.IntervalMathlib.PntTable12LogConformance
