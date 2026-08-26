/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.IntegralCanary
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Checked non-elementary integral acceptance canary

The single-cell degree-seven Taylor certificate is produced by the
Mathlib-free planner and replayed through the generic chronology/frontend.
Its ordinary conclusion bounds `∫ x in 0..1, exp (-x²)` to four decimals.
-/

namespace Hex.IntervalMathlib.IntegralCanaryConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry IntegralCanary

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? : Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain program packages
      checkerInput.initialFacts limits
    | none
  some (TargetRun.drive factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name
  reached : TargetRun.Reached Bound

def fixture? : Option Fixture := do
  let result ← run?
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { session := result.session, registry, reached }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 0, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .window7468_7469 &&
      fixture.session.state.engine.facts == #[.window7468_7469] &&
      fixture.session.state.engine.chronology == #[.fact 0] &&
      fixture.registry.emit.find? integralFactSchema.key == some ``integralFactSchema

#guard baseFacts == [{ node := node 0, fact := .all }]
#guard checkerInput.initialFacts == #[.all]

/-! ## Certificate mutation rejection -/

private def omittedCellBody : List Nat :=
  [0, 0, 1, 1, 1, 8, 1009219, 1351350, 1, 609280,
    7468, 10000, 7469, 10000]

private def wrongErrorBody : List Nat :=
  [1, 0, 1, 1, 1, 8, 1009219, 1351350, 1, 609281,
    7468, 10000, 7469, 10000]

private def wrongEndpointBody : List Nat :=
  [1, 0, 1, 2, 1, 8, 1009219, 1351350, 1, 609280,
    7468, 10000, 7469, 10000]

#guard decodeCertificate? certificateBody == some certificate
#guard (decodeCertificate? omittedCellBody).isNone
#guard (decodeCertificate? wrongErrorBody).isNone
#guard (decodeCertificate? wrongEndpointBody).isNone
#guard factFormat.validateBody certificateBody
#guard !factFormat.validateBody omittedCellBody
#guard !factFormat.validateBody wrongErrorBody
#guard !factFormat.validateBody wrongEndpointBody

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := integrationRuleKey
    node := node 0
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node 0] }

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
    writes := [node 0] }

#guard
  match (planForBody omittedCellBody request).outcome with
  | .failed _ => (planForBody omittedCellBody request).drafts.isEmpty
  | _ => false
#guard
  match (planForBody wrongErrorBody request).outcome with
  | .failed _ => (planForBody wrongErrorBody request).drafts.isEmpty
  | _ => false
#guard
  match (planForBody wrongEndpointBody request).outcome with
  | .failed _ => (planForBody wrongEndpointBody request).drafts.isEmpty
  | _ => false

private def replayContext : RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node := node 0, fact := .window7468_7469 } }

#guard
  (integralFactSchema.replay checkerInput action replayContext certificate).isSome

private def omittedCellCertificate : IntegrationCertificate :=
  { certificate with cells := 0 }

private def wrongErrorCertificate : IntegrationCertificate :=
  { certificate with errorDenominator := 609281 }

private def wrongEndpointCertificate : IntegrationCertificate :=
  { certificate with rightNumerator := 2 }

private def wrongFact : RuleFactContext checkerInput action :=
  { replayContext with proposed := { node := node 0, fact := .all } }

#guard
  (integralFactSchema.replay checkerInput action replayContext
    omittedCellCertificate).isNone
#guard
  (integralFactSchema.replay checkerInput action replayContext
    wrongErrorCertificate).isNone
#guard
  (integralFactSchema.replay checkerInput action replayContext
    wrongEndpointCertificate).isNone
#guard
  (integralFactSchema.replay checkerInput action wrongFact certificate).isNone

/-! ## Generic chronology and ordinary theorem closure -/

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture =>
      Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program &&
      match trace.events with
      | [.rule step] =>
          step.entry.replayKey == integralFactSchema.key &&
            step.event.node == node 0 && step.event.fact == .window7468_7469 &&
            step.assumptions == [] && step.previous == .all &&
            step.entry.body == certificateBody
      | _ => false

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .window7468_7469 => mkConst ``Bound.window7468_7469
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

private meta def emitEvidence : MetaM Expr := do
  let some fixture := fixture?
    | throwError "integral_canary: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "integral_canary: chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "integral_canary: expected exactly one rule event"
  unless trace.program == program &&
      step.entry.replayKey == integralFactSchema.key &&
      step.event.node == node 0 && step.event.fact == .window7468_7469 &&
      step.assumptions == [] && step.entry.body == certificateBody do
    throwError "integral_canary: emitted event drifted from the checked certificate"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target

private noncomputable def replayEvidence : Evidence
    (semantics.Entails program baseFacts checkerInput.target) := by
  run_tac
    let evidence ← emitEvidence
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "integral_canary: replay evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

/-- Four-decimal certified enclosure obtained through generic package planning,
chronological replay, and the proof frontend. -/
theorem gaussianIntegralCanary :
    (7468 : ℝ) / 10000 <
        ∫ x in (0 : ℝ)..1, Real.exp (-(x ^ 2)) ∧
      (∫ x in (0 : ℝ)..1, Real.exp (-(x ^ 2))) < 7469 / 10000 :=
  closeIntegral replayEvidence

/--
info: 'Hex.IntervalMathlib.IntegralCanaryConformance.gaussianIntegralCanary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms gaussianIntegralCanary

end Hex.IntervalMathlib.IntegralCanaryConformance
