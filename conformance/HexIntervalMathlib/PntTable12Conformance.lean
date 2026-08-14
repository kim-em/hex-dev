/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable12
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ Table 12 batch acceptance probe

PNT+ commit `21998bb6196b56789f72a52656a781a75e134eb0` checks 26 rows and five
columns in `BKLNW.table_12_check`.  This representative bounded fixture replays
all five numerical cells of the ordinary row `b = 25` in one provider action.
The other 125 cells, including the two logarithmic rows, remain explicitly
outside this fixture.
-/

namespace Hex.IntervalMathlib.PntTable12Conformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntTable12

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

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
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some
    { session := result.session
      registry
      reached
      events := result.events }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 4, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .row25k5 && fixture.events.size == 1 &&
      fixture.session.state.engine.facts ==
        #[.row25k1, .row25k2, .row25k3, .row25k4, .row25k5, .all] &&
      fixture.session.state.engine.chronology ==
        #[.fact 0, .fact 1, .fact 2, .fact 3, .fact 4] &&
      fixture.session.state.engine.metrics.requests == 1 &&
      fixture.session.state.engine.metrics.replies == 1 &&
      fixture.session.state.engine.metrics.candidates == 5 &&
      fixture.session.state.engine.metrics.improvements == 5 &&
      fixture.session.arena.entries.size == 1 &&
      fixture.registry.emit.find? batchFactSchema.key == some ``batchFactSchema

#guard
  baseFacts ==
      [{ node := node 0, fact := .all }, { node := node 1, fact := .all },
        { node := node 2, fact := .all }, { node := node 3, fact := .all },
        { node := node 4, fact := .all }, { node := node 5, fact := .all }] &&
    checkerInput.initialFacts == #[.all, .all, .all, .all, .all, .all]

/-! ## Coordinate diagnostics and payload mutation -/

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := batchRuleKey
    node := node 5
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node 0, node 1, node 2, node 3, node 4] }

private def programView : ProgramView :=
  { programVersion := 0
    operations := program.operations
    nodes := program.nodes
    generations := #[0, 0, 0, 0, 0, 0]
    depths := #[0, 0, 0, 0, 0, 1] }

private def request : RuleRequest Bound :=
  { action
    program := programView
    inputs := []
    writes := [node 0, node 1, node 2, node 3, node 4] }

#guard decodeCertificate? rowBody == some rowCertificate
#guard (decodeCertificate? paperBody).isNone
#guard factFormat.validateBody rowBody
#guard !factFormat.validateBody paperBody
#guard coordinateCode paperCell == 205
#guard paperCellForCode? 205 == some paperCell
#guard (paperCellForCode? 204).isNone

-- Runtime intersection follows the mathematical nesting of the five upper
-- cuts, even for fact combinations that this fixed chronology never reaches.
#guard Bound.meet .row25k1 .row25k5 == .row25k1
#guard Bound.meet .row25k5 .row25k1 == .row25k1
#guard
  match factDomain.narrow real .row25k5 .row25k1 with
  | .improved .row25k1 => true
  | _ => false
#guard
  (boundSchema.proveMeet program (node 0) .row25k5 .row25k1 .row25k1).isSome
#guard
  (boundSchema.proveMeet program (node 0) .row25k5 .row25k1 .empty).isNone

-- These are the exact fixed row identity fields carried by the payload, not
-- parameters accepted from an arbitrary Table 12 row.
#guard rowCertificate.row == 25 && rowCertificate.columns == 5
#guard
  rowCertificate.cNumerator == 88 && rowCertificate.cDenominator == 100 &&
    rowCertificate.capitalNumerator == 86 &&
    rowCertificate.capitalDenominator == 100 &&
    rowCertificate.cZeroNumerator == 103883 &&
    rowCertificate.cZeroDenominator == 100000
#guard
  rowCertificate.cell1Mantissa == 1750020 && rowCertificate.cell1Scale == 10 &&
    rowCertificate.cell2Mantissa == 4375050 && rowCertificate.cell2Scale == 9 &&
    rowCertificate.cell3Mantissa == 1093770 && rowCertificate.cell3Scale == 7 &&
    rowCertificate.cell4Mantissa == 2734410 && rowCertificate.cell4Scale == 6 &&
    rowCertificate.cell5Mantissa == 6836010 && rowCertificate.cell5Scale == 5
#guard rowCertificate.mMantissa == 32 && rowCertificate.mExponent == 12

-- The false paper entry is an incompatible coordinate-specific enclosure,
-- never a resource limit or a request for greater precision.
#guard
  match (planForBody paperBody request).outcome with
  | .failed diagnostic =>
      diagnostic == coordinateCode paperCell &&
        paperCellForCode? diagnostic == some paperCell
  | _ => false

#guard (planForBody paperBody request).drafts.isEmpty

private def context (target : NodeId) (fact : Bound) :
    RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node := target, fact } }

#guard
  (batchFactSchema.replay checkerInput action (context (node 0) .row25k1)
    rowCertificate).isSome
#guard
  (batchFactSchema.replay checkerInput action (context (node 1) .row25k2)
    rowCertificate).isSome
#guard
  (batchFactSchema.replay checkerInput action (context (node 2) .row25k3)
    rowCertificate).isSome
#guard
  (batchFactSchema.replay checkerInput action (context (node 3) .row25k4)
    rowCertificate).isSome
#guard
  (batchFactSchema.replay checkerInput action (context (node 4) .row25k5)
    rowCertificate).isSome

private def paperCertificate : RowCertificate :=
  { rowCertificate with cell5Mantissa := 6653500 }

#guard
  (batchFactSchema.replay checkerInput action (context (node 4) .row25k5)
    paperCertificate).isNone
#guard
  (batchFactSchema.replay checkerInput action (context (node 3) .row25k5)
    rowCertificate).isNone
#guard
  (batchFactSchema.replay checkerInput action (context (node 4) .row25k4)
    rowCertificate).isNone

/-! ## Five-event bounded chronology and generic closure -/

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture =>
      Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program && trace.events.length == 5 &&
      trace.events.all fun event =>
        match event with
        | .rule step =>
            step.entry.replayKey == batchFactSchema.key &&
              step.event.programVersion == 0 && step.event.version == 1 &&
              step.assumptions.isEmpty && step.previous == .all &&
              step.entry.body == rowBody
        | _ => false

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .row25k1 => mkConst ``Bound.row25k1
  | .row25k2 => mkConst ``Bound.row25k2
  | .row25k3 => mkConst ``Bound.row25k3
  | .row25k4 => mkConst ``Bound.row25k4
  | .row25k5 => mkConst ``Bound.row25k5
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

private meta def emitEvidence (target : NodeId) (fact : Bound) : MetaM Expr := do
  let some fixture := fixture?
    | throwError "pnt_table12: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_table12: chronology quotation failed"
  unless trace.program == program && trace.events.length == 5 do
    throwError "pnt_table12: expected the exact five-cell chronology"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state
    { node := target, version := 1 } fact { node := target, fact }

private noncomputable def replayCell1 : Evidence
    (semantics.Entails program baseFacts { node := node 0, fact := .row25k1 }) := by
  run_tac
    let evidence ← emitEvidence (node 0) .row25k1
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12: cell (25,1) evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

private noncomputable def replayCell2 : Evidence
    (semantics.Entails program baseFacts { node := node 1, fact := .row25k2 }) := by
  run_tac
    let evidence ← emitEvidence (node 1) .row25k2
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12: cell (25,2) evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

private noncomputable def replayCell3 : Evidence
    (semantics.Entails program baseFacts { node := node 2, fact := .row25k3 }) := by
  run_tac
    let evidence ← emitEvidence (node 2) .row25k3
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12: cell (25,3) evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

private noncomputable def replayCell4 : Evidence
    (semantics.Entails program baseFacts { node := node 3, fact := .row25k4 }) := by
  run_tac
    let evidence ← emitEvidence (node 3) .row25k4
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12: cell (25,4) evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

private noncomputable def replayCell5 : Evidence
    (semantics.Entails program baseFacts { node := node 4, fact := .row25k5 }) := by
  run_tac
    let evidence ← emitEvidence (node 4) .row25k5
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table12: cell (25,5) evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

/-- The five numerical leaves of the pinned ordinary row, closed from one
checked row payload and its five-event generic replay fold. -/
theorem table12Row25 :
    row25Value 1 ≤ 1.750020e-4 ∧ row25Value 2 ≤ 4.375050e-3 ∧
      row25Value 3 ≤ 1.093770e-1 ∧ row25Value 4 ≤ 2.734410e0 ∧
      row25Value 5 ≤ 6.836010e1 := by
  have replayed :=
    closeRow25 replayCell1 replayCell2 replayCell3 replayCell4 replayCell5
  norm_num [OfScientific.ofScientific] at replayed ⊢
  exact replayed

/--
info: 'Hex.IntervalMathlib.PntTable12Conformance.table12Row25' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms table12Row25

/--
info: 'Hex.Interval.Experiment.PntTable12.rejectPaperCell' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rejectPaperCell

end Hex.IntervalMathlib.PntTable12Conformance
