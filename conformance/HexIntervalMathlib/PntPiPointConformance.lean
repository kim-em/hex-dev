/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntPiPoint
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ π upper bound

The Mathlib-free action authenticates a provider-agnostic π operation and the
exact rational cut `315 / 100`.  Ordinary-kernel replay supplies Mathlib's
proved `Real.pi_lt_d2`; no Chudnovsky or LeanCert theorem is imported.
-/

namespace Hex.IntervalMathlib.PntPiPointConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntPiPoint

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view => match view.offers[0]? with
      | some offer => .select offer state | none => .stop state }

private def run? : Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain checkerInput.baseProgram
      packages checkerInput.initialFacts limits | none
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
    fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .upper certificate.cut &&
      fixture.session.state.engine.facts == #[.request, .upper certificate.cut] &&
      fixture.session.state.engine.chronology == #[.fact 0] &&
      fixture.registry.emit.find? factSchema.key == some ``factSchema

def trace? : Option (Frontend.Trace Bound) :=
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace => trace.program == program &&
    match trace.events with
    | [.rule step] =>
        step.entry.replayKey == factSchema.key &&
          step.entry.body == encode certificate &&
          step.assumptions == [{ node := node 0, fact := .request }] &&
          step.event.node == node 1 &&
          step.event.fact == .upper certificate.cut
    | _ => false

/-! ## Mutation rejection -/

private def action : Action :=
  { serial := 0, programVersion := 0, application := { index := 0 },
    rule := { index := 0 }, key := ruleKey, node := node 1, kind := .forward,
    effort := 0, generation := 0, inputs := [], writes := [node 1] }
private def context : RuleFactContext checkerInput action :=
  { program, basePrefix := ProgramPrefix.refl program,
    assumptions := [{ node := node 0, fact := .request }],
    proposed := { node := node 1, fact := .upper certificate.cut } }

private def falseEndpoint : Certificate := { numerator := 3, denominator := 1 }
private def wrongSource : RuleFactContext checkerInput action :=
  { context with assumptions := [{ node := node 0, fact := .all }] }
private def wrongCut : RuleFactContext checkerInput action :=
  { context with proposed :=
      { node := node 1, fact := .upper falseEndpoint.cut } }

#guard decode? (encode certificate) == some certificate
#guard (decode? (encode falseEndpoint)).isNone
#guard (factSchema.replay checkerInput action context certificate).isSome
#guard (factSchema.replay checkerInput action wrongSource certificate).isNone
#guard (factSchema.replay checkerInput action wrongCut certificate).isNone
#guard (factSchema.replay checkerInput action context falseEndpoint).isNone

theorem rejectFalseEndpoint : ¬ Real.pi < 3 := by
  exact not_lt_of_ge Real.pi_gt_three.le

/--
info: 'Real.pi_lt_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.pi_lt_d2

/--
info: 'Hex.Interval.Experiment.PntPiPoint.pi_le_3_15' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntPiPoint.pi_le_3_15

/-! ## Generic proof emission -/

private def cutExpr (value : Cut) : Expr :=
  mkApp2 (mkConst ``Cut.mk) (mkNatLit value.numerator) (mkNatLit value.denominator)
private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .request => mkConst ``Bound.request
  | .upper value => mkApp (mkConst ``Bound.upper) (cutExpr value)
  | .empty => mkConst ``Bound.empty
private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))
private def seedAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence (semantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found
private def frontendContext : ProofFrontend.Context Bound Name :=
  { encoder := boundEncoder, resolveSchema := pure,
    semantics := mkConst ``semantics, domain := mkConst ``boundSchema,
    laws := mkConst ``laws, stableLaw := mkConst ``stableLaw,
    input := mkConst ``checkerInput, assumed := ``seedAssumed,
    baseFacts, baseFactsTerm := mkConst ``baseFacts,
    baseProgram := program, baseProgramTerm := mkConst ``program,
    basePrefix := mkConst ``basePrefix, baseWithin := mkConst ``baseWithin,
    initialExtension := mkConst ``initialExtension,
    finalPrefix := mkConst ``basePrefix, sameOperations := mkConst ``sameOperations,
    top := boundSchema.top }

private meta def emitEvidence : MetaM Expr := do
  let some fixture := fixture?
    | throwError "pnt_pi_point: search or registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_pi_point: chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "pnt_pi_point: expected one rule event"
  unless step.entry.replayKey == factSchema.key &&
      step.entry.body == encode certificate &&
      step.assumptions == [{ node := node 0, fact := .request }] do
    throwError "pnt_pi_point: emitted certificate drifted"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target

/-- `π < 3.15` emitted through the generic checked proof frontend. -/
theorem pntPi : Real.pi < (3.15 : ℝ) := by
  run_tac
    let evidence ← emitEvidence
    let proof ← mkAppM ``closePi #[evidence]
    let goal ← getMainGoal
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "pnt_pi_point: closed replay has the wrong theorem"
    goal.assign (← instantiateMVars proof)
    replaceMainGoal []

/--
info: 'Hex.IntervalMathlib.PntPiPointConformance.pntPi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntPi

end Hex.IntervalMathlib.PntPiPointConformance
