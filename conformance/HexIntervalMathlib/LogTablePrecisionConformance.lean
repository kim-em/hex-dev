/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.LogTablePrecision
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Precision-indexed logarithm-table conformance

The same package answers 20- and 50-decimal requests with different certified
term counts. The 50-decimal chronology is emitted through the generic proof
frontend to an ordinary theorem about `Real.log 2`.
-/

namespace Hex.IntervalMathlib.LogTablePrecisionConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend FrontendEncoder ProofFrontend ProofRegistry
open Hex.Interval.Experiment.LogTablePrecision
open Hex.IntervalMathlib.Experiment.LogTablePrecision

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? (input : CheckerInput Bound) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := Session.start factDomain input.baseProgram packages
      input.initialFacts limits
    | none
  some (TargetRun.drive factDomain input.target.node input.target.fact
    firstOffer limits.policy.maxDecisions session ())

private structure Fixture where
  result : TargetRun.Result Bound Unit
  reached : TargetRun.Reached Bound
  registry : ProofRegistry.Registry semantics Name

private def fixture? : Option Fixture := do
  let result ← run? decimal50Input
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { result, reached, registry }

#guard fixture?.any fun fixture =>
  fixture.reached.seen == ({ node := node 2, version := 1 } : SeenVersion) &&
    fixture.reached.fact == decimal50Fact &&
    fixture.result.session.state.engine.facts ==
      #[.two, decimal50Request, decimal50Fact] &&
    fixture.result.session.state.engine.chronology == #[.fact 0] &&
    fixture.registry.emit.find? logFactSchema.key == some ``logFactSchema

-- A lower precision request drives the same package to a smaller term count
-- and its correspondingly wider certified window.
#guard (run? decimal20Input).any fun result =>
  match result.stop with
  | .target reached =>
      reached.seen == ({ node := node 2, version := 1 } : SeenVersion) &&
        reached.fact == decimal20Fact &&
        result.session.state.engine.facts ==
          #[.two, decimal20Request, decimal20Fact] &&
        result.session.state.engine.chronology == #[.fact 0]
  | _ => false

private def traceFor? (input : CheckerInput Bound) : Option (Frontend.Trace Bound) :=
  match run? input with
  | none => none
  | some result =>
      Frontend.trace? result.session.state.engine result.session.arena

private def trace? : Option (Frontend.Trace Bound) := traceFor? decimal50Input

#guard (traceFor? decimal20Input).any fun trace =>
  match trace.events with
  | [.rule step] =>
      step.event.fact == decimal20Fact &&
        step.entry.body == certificateBody decimal20Certificate
  | _ => false

#guard trace?.any fun trace =>
  trace.program == program &&
    match trace.events with
    | [.rule step] =>
        step.event.node == node 2 && step.event.fact == decimal50Fact &&
          step.entry.body == certificateBody decimal50Certificate &&
          match step.event.cause with
          | .rule action _ _ =>
              action.key == logRuleKey &&
                action.inputs ==
                  [{ node := node 0, version := 0 },
                   { node := node 1, version := 0 }]
          | .transport _ _ => false
    | _ => false

private def logAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := logRuleKey
    node := node 2
    kind := .forward
    effort := 0
    inputs := []
    writes := [node 2] }

private def logContext : RuleFactContext decimal50Input logAction :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions :=
      [{ node := node 0, fact := .two },
       { node := node 1, fact := decimal50Request }]
    proposed := { node := node 2, fact := decimal50Fact } }

private def insufficientTerms : Certificate :=
  { decimal50Certificate with terms := 52 }

private def wrongEndpoint : Certificate :=
  { decimal50Certificate with
      upperNumerator :=
        69314718055994530941723212145817656807550013436027 }

private def wrongPrecision : Certificate :=
  { decimal50Certificate with digits := 49 }

#guard (decodeCertificate? (certificateBody insufficientTerms)).isSome
#guard (decodeCertificate? (certificateBody wrongEndpoint)).isSome
#guard (decodeCertificate? (certificateBody wrongPrecision)).isSome
#guard (logFactSchema.replay decimal50Input logAction logContext
  insufficientTerms).isNone
#guard (logFactSchema.replay decimal50Input logAction logContext
  wrongEndpoint).isNone
#guard (logFactSchema.replay decimal50Input logAction logContext
  wrongPrecision).isNone
#guard (logFactSchema.replay decimal50Input logAction logContext
  decimal50Certificate).isSome

private def wrongSourceContext : RuleFactContext decimal50Input logAction :=
  { logContext with
    assumptions :=
      [{ node := node 0, fact := .all },
       { node := node 1, fact := decimal50Request }] }

#guard (logFactSchema.replay decimal50Input logAction wrongSourceContext
  decimal50Certificate).isNone

private def boundExpr? : Bound → Option Expr
  | .all => some (mkConst ``Bound.all)
  | .two => some (mkConst ``Bound.two)
  | fact =>
      if fact == decimal50Request then some (mkConst ``decimal50Request)
      else if fact == decimal50Fact then some (mkConst ``decimal50Fact)
      else none

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) fun fact =>
    match boundExpr? fact with
    | some expression => pure expression
    | none => throwError "log-table-precision: unrecognized fact"

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
    input := mkConst ``decimal50Input
    assumed := ``seedAssumed
    baseFacts
    baseFactsTerm := mkConst ``baseFacts
    baseProgram := program
    baseProgramTerm := mkConst ``program
    basePrefix := mkConst ``basePrefix
    baseWithin := mkConst ``baseWithin
    initialExtension := mkConst ``initialExtension
    finalPrefix := mkConst ``programPrefix
    sameOperations := mkConst ``sameOperations
    top := boundSchema.top }

private meta def emitEvidence : MetaM Expr := do
  let some fixture := fixture?
    | throwError "log-table-precision: search or proof registry failed"
  let some trace := Frontend.trace? fixture.result.session.state.engine
      fixture.result.session.arena
    | throwError "log-table-precision: chronology quotation failed"
  unless trace.program == program do
    throwError "log-table-precision: unexpected graph"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  let final ← ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact decimal50Input.target
  mkAppM ``closeEvidence #[final]

syntax (name := intervalLogTablePrecisionTac) "interval_log_table_precision" : tactic

@[tactic intervalLogTablePrecisionTac] meta def evalIntervalLogTablePrecision :
    Tactic := fun stx => do
  match stx with
  | `(tactic| interval_log_table_precision) =>
      let goal ← getMainGoal
      goal.withContext do
        let evidence ← emitEvidence
        let proof ← mkAppM ``Evidence.proof
          #[evidence, mkConst ``valuation, mkConst ``valuationModels, mkConst ``baseHolds]
        unless ← isDefEq (← inferType proof) (← goal.getType) do
          throwError "log-table-precision: emitted proof has the wrong target"
        goal.assign (← instantiateMVars proof)
        replaceMainGoal []
  | _ => throwUnsupportedSyntax

private theorem endpointFact : Contains decimal50Fact (Real.log 2) := by
  interval_log_table_precision

/-- The 50-decimal request produces an ordinary strict enclosure theorem. -/
theorem logTwoDecimal50 :
    (69314718055994530941723212145817656807550013436025 / 10 ^ 50 : ℝ) <
        Real.log 2 ∧
      Real.log 2 <
        (69314718055994530941723212145817656807550013436026 / 10 ^ 50 : ℝ) := by
  have result := endpointFact
  norm_num [Contains, decimal50Fact, Certificate.window,
    decimal50Certificate, ratio] at result ⊢
  exact result

/--
info: 'Hex.IntervalMathlib.LogTablePrecisionConformance.logTwoDecimal50' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms logTwoDecimal50

end Hex.IntervalMathlib.LogTablePrecisionConformance
