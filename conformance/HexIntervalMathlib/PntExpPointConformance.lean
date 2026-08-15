/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntExpPoint
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ exponential point bounds

This fixture covers the nine remaining exponential tactic sites in pinned
PNT+ `IEANTN/LogTables.lean`. Every row uses one authenticated rational Taylor
step and natural-power reduction; the tight `exp 20` row also crosses generic
chronology and `ProofFrontend` replay.
-/

namespace Hex.IntervalMathlib.PntExpPointConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntExpPoint

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? (value : Certificate) : Option (TargetRun.Result Bound Unit) := do
  let input := checkerInput value
  let .ok session := PolicySession.Session.start factDomain input.baseProgram
      packages input.initialFacts limits | none
  some (TargetRun.drive factDomain input.target.node input.target.fact firstOffer
    limits.policy.maxDecisions session ())

#guard rows.length == 9
#guard rows.all Certificate.valid
#guard rows.all fun value => rowFor? value.sourceIndex == some value
#guard rows.all fun value => decode? (encode value) == some value
#guard rows.all fun value => factFormat.validateBody (encode value)
#guard rows.all fun value =>
  (run? value).any fun result =>
    match result.stop with
    | .target reached =>
        reached.fact == value.result && result.events.size == 1 &&
          result.session.state.engine.chronology == #[.fact 0]
    | _ => false

private def unknown : Certificate := { rowTwenty with sourceIndex := 9 }

#guard
  (run? unknown).any fun result =>
    match result.stop with
    | .saturated => result.events.size == 1 &&
        result.session.state.engine.chronology.isEmpty &&
        result.session.arena.entries.isEmpty
    | _ => false

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name
  reached : TargetRun.Reached Bound

def fixture? : Option Fixture := do
  let result ← run? rowTwenty
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { session := result.session, registry, reached }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == rowTwenty.result &&
      fixture.registry.emit.find? factSchema.key == some ``factSchema

def trace? : Option (Frontend.Trace Bound) :=
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program &&
      match trace.events with
      | [.rule step] =>
          step.entry.replayKey == factSchema.key &&
            step.entry.body == encode rowTwenty &&
            step.assumptions == [{ node := node 0, fact := .exact rowTwenty.source }] &&
            step.event.node == node 1 && step.event.fact == rowTwenty.result &&
            step.previous == .all
      | _ => false

/-! ## Mutation rejection -/

private def action : Action :=
  { serial := 0, programVersion := 0, application := { index := 0 },
    rule := { index := 0 }, key := ruleKey, node := node 1, kind := .forward,
    effort := 0, generation := 0, inputs := [], writes := [node 1] }

private def replayContext : RuleFactContext representativeInput action :=
  { program, basePrefix := ProgramPrefix.refl program,
    assumptions := [{ node := node 0, fact := .exact rowTwenty.source }],
    proposed := { node := node 1, fact := rowTwenty.result } }

private def insufficientTerms : Certificate := { rowTwenty with terms := 13 }
private def wrongStep : Certificate := { rowTwenty with stepNumerator := 2 }
private def wrongPower : Certificate := { rowTwenty with power := 39 }
private def wrongSource : Certificate := { rowTwenty with sourceNumerator := 21 }
private def falseEndpoint : Certificate := { rowTwenty with resultNumerator := 1 }

#guard (decode? (encode insufficientTerms)).isNone
#guard (decode? (encode wrongStep)).isNone
#guard (decode? (encode wrongPower)).isNone
#guard (decode? (encode wrongSource)).isNone
#guard (decode? (encode falseEndpoint)).isNone
#guard (factSchema.replay representativeInput action replayContext rowTwenty).isSome
#guard (factSchema.replay representativeInput action replayContext rowTwentyTwo).isNone
#guard (factSchema.replay representativeInput action replayContext falseEndpoint).isNone

private def crossSource : RuleFactContext representativeInput action :=
  { replayContext with assumptions :=
      [{ node := node 0, fact := .exact rowTwentyTwo.source }] }
private def crossCut : RuleFactContext representativeInput action :=
  { replayContext with proposed := { node := node 1, fact := rowTwentyTwo.result } }

#guard (factSchema.replay representativeInput action crossSource rowTwenty).isNone
#guard (factSchema.replay representativeInput action crossCut rowTwenty).isNone

theorem rejectFalseEndpoint : ¬ Real.exp 20 < 1 := by
  exact not_lt_of_ge (Real.one_le_exp (by norm_num))

/--
info: 'Hex.Interval.Experiment.PntExpPoint.exp_neg_one_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntExpPoint.exp_neg_one_gt

/--
info: 'Hex.Interval.Experiment.PntExpPoint.inv_900000_le_exp_neg_13_5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms PntExpPoint.inv_900000_le_exp_neg_13_5

/-! ## Generic proof emission and ordinary theorem closure -/

private def sourceExpr (value : Source) : Expr :=
  mkApp4 (mkConst ``Source.mk) (mkNatLit value.sourceIndex)
    (toExpr value.negative) (mkNatLit value.numerator) (mkNatLit value.denominator)
private def cutExpr (value : Cut) : Expr :=
  mkApp3 (mkConst ``Cut.mk) (mkNatLit value.sourceIndex)
    (mkNatLit value.numerator) (mkNatLit value.denominator)
private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .exact value => mkApp (mkConst ``Bound.exact) (sourceExpr value)
  | .lower value => mkApp (mkConst ``Bound.lower) (cutExpr value)
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
    input := mkConst ``representativeInput, assumed := ``seedAssumed,
    baseFacts, baseFactsTerm := mkConst ``baseFacts,
    baseProgram := program, baseProgramTerm := mkConst ``program,
    basePrefix := mkConst ``basePrefix, baseWithin := mkConst ``baseWithin,
    initialExtension := mkConst ``initialExtension,
    finalPrefix := mkConst ``basePrefix, sameOperations := mkConst ``sameOperations,
    top := boundSchema.top }

private meta def emitEvidence : MetaM Expr := do
  let some fixture := fixture?
    | throwError "pnt_exp_point: search or registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_exp_point: chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "pnt_exp_point: expected one rule event"
  unless step.entry.replayKey == factSchema.key &&
      step.entry.body == encode rowTwenty &&
      step.assumptions == [{ node := node 0, fact := .exact rowTwenty.source }] do
    throwError "pnt_exp_point: emitted row drifted"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact representativeInput.target

/-- Representative ordinary-kernel theorem emitted through generic checked replay. -/
theorem pntExpTwenty : Real.exp 20 < 485165196 := by
  run_tac
    let evidence ← emitEvidence
    let proof ← mkAppM ``closeExpTwenty #[evidence]
    let goal ← getMainGoal
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "pnt_exp_point: closed replay has the wrong theorem"
    goal.assign (← instantiateMVars proof)
    replaceMainGoal []

/--
info: 'Hex.IntervalMathlib.PntExpPointConformance.pntExpTwenty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntExpTwenty

end Hex.IntervalMathlib.PntExpPointConformance
