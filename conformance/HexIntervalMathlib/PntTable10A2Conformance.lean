/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntTable10A2
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Checked PNT+ BKLNW Table 10 `a₂` acceptance

One source-indexed schema covers all 38 head-plus-tail declarations.  The
runtime authenticates every row and the generic replay theorem closes a
representative source theorem through `ProofFrontend`.
-/

namespace Hex.IntervalMathlib.PntTable10A2Conformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntTable10A2

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? (value : Certificate) : Option (TargetRun.Result Bound Unit) := do
  let .ok session := start value | none
  some (TargetRun.drive factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer (limitsFor value).policy.maxDecisions session ())

set_option exponentiation.threshold 500 in
#guard certificates.length == 38
set_option exponentiation.threshold 500 in
#guard row21.argument == 21 && row21.floor == 30 &&
  row21.targetNumerator == 14394 && row21.targetDenominator == 10000
set_option exponentiation.threshold 500 in
#guard row59.argument == 59 && row59.floor == 85 &&
  row59.targetNumerator == 10280 && row59.targetDenominator == 10000
set_option exponentiation.threshold 500 in
#guard certificates.all fun value => value.argument != 20 && value.argument != 25
set_option exponentiation.threshold 500 in
#guard certificates.all validCertificate
set_option exponentiation.threshold 500 in
#guard certificates.all fun value =>
  decodeCertificate? (certificateBody value) == some value
set_option exponentiation.threshold 500 in
#guard certificates.all fun value => factFormat.validateBody (certificateBody value)
set_option exponentiation.threshold 500 in
#guard certificates.all fun value =>
  (run? value).any fun result =>
    match result.stop with
    | .target reached => reached.fact == .upper
    | _ => false

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := foldRuleKey
    node
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node] }

private def programView : ProgramView :=
  { programVersion := 0
    operations := program.operations
    nodes := program.nodes
    generations := #[0]
    depths := #[0] }

private def request : RuleRequest Bound :=
  { action
    program := programView
    inputs := []
    writes := [node] }

private def planFails (value : Certificate) : Bool :=
  match (planForBody (certificateBody value) request).outcome with
  | .failed _ => (planForBody (certificateBody value) request).drafts.isEmpty
  | _ => false

private def wrongSource : Certificate := { row21 with sourceIndex := 1 }
private def wrongArgument : Certificate := { row21 with argument := 22 }
private def wrongFloor : Certificate := { row21 with floor := 31 }
private def wrongLogLower : Certificate := { row21 with logLower := logLowerNumerator + 1 }
private def wrongLogUpper : Certificate := { row21 with logUpper := logUpperNumerator - 1 }
private def wrongLogScale : Certificate := { row21 with logScale := 10 ^ 19 }
private def wrongBaseScale : Certificate := { row21 with baseScale := 10 ^ 11 }
private def wrongEndpoint : Certificate :=
  { row21 with targetNumerator := 1, targetDenominator := 1 }

private def mutations : List Certificate :=
  [wrongSource, wrongArgument, wrongFloor, wrongLogLower, wrongLogUpper,
    wrongLogScale, wrongBaseScale, wrongEndpoint]

set_option exponentiation.threshold 500 in
#guard mutations.all fun value =>
  (decodeCertificate? (certificateBody value)).isSome
set_option exponentiation.threshold 500 in
#guard mutations.all fun value => !factFormat.validateBody (certificateBody value)
set_option exponentiation.threshold 500 in
#guard mutations.all planFails

private def replayContext : RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node, fact := .upper } }

set_option exponentiation.threshold 500 in
#guard certificates.all fun value =>
  ((foldFactSchema value).replay checkerInput action replayContext value).isSome

/- A valid row cannot be replayed against another source model. -/
#guard
  ((foldFactSchema row21).replay checkerInput action replayContext row59).isNone
#guard
  ((foldFactSchema row21).replay checkerInput action replayContext wrongFloor).isNone

private def wrongFact : RuleFactContext checkerInput action :=
  { replayContext with proposed := { node, fact := .all } }

#guard ((foldFactSchema row21).replay checkerInput action wrongFact row21).isNone

/- The mutated endpoint is mathematically false, not merely absent from the
source table. -/
theorem rejectEndpoint :
    ¬ sourceA2 row21.argument ≤ (1 : ℝ) := by
  have valid : Valid row21 := by
    set_option exponentiation.threshold 500 in decide
  have floorEq := sourceFloor row21 valid
  have powerLower : 1 ≤
      PntBKLNWPow.sourceF ((2 : ℝ) ^ (row21.floor + 1)) :=
    PntBKLNWPow.oneLeSourcePow (by
      norm_num [row21, certificateFor?, sourceRecord?])
  intro claimed
  unfold sourceA2 at claimed
  rw [floorEq] at claimed
  have maxLower : 1 ≤
      max (PntBKLNWPow.sourceF (Real.exp row21.argument))
        (PntBKLNWPow.sourceF ((2 : ℝ) ^ (row21.floor + 1))) :=
    powerLower.trans (le_max_right _ _)
  norm_num at claimed
  nlinarith

/-! ## Generic chronology and ordinary theorem closure -/

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry (semantics row21) Lean.Name
  reached : TargetRun.Reached Bound

def fixture? : Option Fixture := do
  let result ← run? row21
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry
      row21ProofPackages | none
  some { session := result.session, registry, reached }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .upper &&
      fixture.session.state.engine.facts == #[.upper] &&
      fixture.session.state.engine.chronology == #[.fact 0] &&
      fixture.registry.emit.find? row21FactSchema.key ==
        some ``row21FactSchema

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program &&
      match trace.events with
      | [.rule step] =>
          step.entry.replayKey == row21FactSchema.key &&
            step.event.node == node && step.event.fact == .upper &&
            step.assumptions == [] && step.previous == .all &&
            step.entry.body == certificateBody row21
      | _ => false

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .upper => mkConst ``Bound.upper
  | .empty => mkConst ``Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))

private def seedAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence ((semantics row21).Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def frontendContext : ProofFrontend.Context Bound Name :=
  { encoder := boundEncoder
    resolveSchema := pure
    semantics := mkApp (mkConst ``semantics) (mkConst ``row21)
    domain := mkApp (mkConst ``boundSchema) (mkConst ``row21)
    laws := mkApp (mkConst ``laws) (mkConst ``row21)
    stableLaw := mkApp (mkConst ``stableLaw) (mkConst ``row21)
    input := mkConst ``checkerInput
    assumed := ``seedAssumed
    baseFacts
    baseFactsTerm := mkConst ``baseFacts
    baseProgram := program
    baseProgramTerm := mkConst ``program
    basePrefix := mkConst ``basePrefix
    baseWithin := mkConst ``baseWithin
    initialExtension := mkApp (mkConst ``initialExtension) (mkConst ``row21)
    finalPrefix := mkConst ``basePrefix
    sameOperations := mkConst ``sameOperations
    top := (boundSchema row21).top }

private meta def emitEvidence : MetaM Expr := do
  let some fixture := fixture?
    | throwError "pnt_table10_a2: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_table10_a2: chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "pnt_table10_a2: expected exactly one rule event"
  unless trace.program == program &&
      step.entry.replayKey == row21FactSchema.key &&
      step.event.node == node && step.event.fact == .upper &&
      step.assumptions == [] && step.entry.body == certificateBody row21 do
    throwError "pnt_table10_a2: emitted event drifted from the checked certificate"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target

private noncomputable def replayEvidence : Evidence
    ((semantics row21).Entails program baseFacts checkerInput.target) := by
  run_tac
    let evidence ← emitEvidence
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_table10_a2: replay evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

/-- Row 21 closes through generic package planning, chronological replay, and
`ProofFrontend`; the same checked schema accepts all 38 source records. -/
theorem pntTable10A2Row21 :
    sourceA2 row21.argument ≤
      (row21.targetNumerator : ℝ) / row21.targetDenominator :=
  closeUpper row21 replayEvidence

/--
info: 'Hex.IntervalMathlib.PntTable10A2Conformance.pntTable10A2Row21' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pntTable10A2Row21

/--
info: 'Hex.Interval.Experiment.PntTable10A2.certificateUpper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms certificateUpper

/--
info: 'Hex.Interval.Experiment.PntTable10A2.rowOfMem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rowOfMem

/--
info: 'Hex.IntervalMathlib.PntTable10A2Conformance.rejectEndpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rejectEndpoint

end Hex.IntervalMathlib.PntTable10A2Conformance
