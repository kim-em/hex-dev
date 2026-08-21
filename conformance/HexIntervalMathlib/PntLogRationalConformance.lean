/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntLogRational
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ rational logarithm table

This fixture covers seventeen direct logarithm declarations over fifteen exact
rational inputs in PNT+ `IEANTN/LogTables.lean` at commit
`21998bb6196b56789f72a52656a781a75e134eb0`. Every row uses the same bounded
dyadic/atanh provider; the large-shift `32e12` row also crosses generic
chronology and `ProofFrontend` replay.
-/

namespace Hex.IntervalMathlib.PntLogRationalConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntLogRational

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

#guard rows.length == 15
#guard rows.all Certificate.valid
#guard rows.all fun value => rowFor? value.sourceIndex == some value
#guard rows.all fun value => decode? (encode value) == some value
#guard rows.all fun value => factFormat.validateBody (encode value)
#guard rows.all fun value =>
  (run? value).any fun result =>
    match result.stop with
    | .target reached =>
        reached.fact == .window value.window && result.events.size == 1 &&
          result.session.state.engine.chronology == #[.fact 0]
    | _ => false

private def unknown : Certificate := { row32e12 with sourceIndex := 15 }

-- An unpinned source/input pair saturates without drafting evidence.
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
  let result ← run? row32e12
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { session := result.session, registry, reached }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .window row32e12.window &&
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
            step.entry.body == encode row32e12 &&
            step.assumptions == [{ node := node 0, fact := .exact row32e12.input }] &&
            step.event.node == node 1 &&
            step.event.fact == .window row32e12.window && step.previous == .all
      | _ => false

/-! ## Mutation rejection -/

private def action : Action :=
  { serial := 0, programVersion := 0, application := { index := 0 },
    rule := { index := 0 }, key := ruleKey, node := node 1, kind := .forward,
    effort := 0, generation := 0, inputs := [], writes := [node 1] }

private def replayContext : RuleFactContext representativeInput action :=
  { program, basePrefix := ProgramPrefix.refl program,
    assumptions := [{ node := node 0, fact := .exact row32e12.input }],
    proposed := { node := node 1, fact := .window row32e12.window } }

private def insufficientTerms : Certificate := { row32e12 with terms := 7 }
private def wrongReduction : Certificate := { row32e12 with shift := 43 }
private def wrongInput : Certificate := { row32e12 with inputNumerator := 32000000000001 }
private def falseEndpoint : Certificate :=
  { row32e12 with lower := 310967571, upper := 310967572 }

#guard (decode? (encode insufficientTerms)).isNone
#guard (decode? (encode wrongReduction)).isNone
#guard (decode? (encode wrongInput)).isNone
#guard (decode? (encode falseEndpoint)).isNone
#guard (factSchema.replay representativeInput action replayContext row32e12).isSome
#guard (factSchema.replay representativeInput action replayContext row5e10).isNone
#guard (factSchema.replay representativeInput action replayContext falseEndpoint).isNone

private def wrongSource : RuleFactContext representativeInput action :=
  { replayContext with assumptions := [{ node := node 0, fact := .exact row5e10.input }] }
private def wrongWindow : RuleFactContext representativeInput action :=
  { replayContext with proposed := { node := node 1, fact := .window row5e10.window } }

#guard (factSchema.replay representativeInput action wrongSource row32e12).isNone
#guard (factSchema.replay representativeInput action wrongWindow row32e12).isNone

theorem rejectFalseEndpoint : ¬ (31.0967571 : ℝ) < Real.log 32e12 := by
  exact not_lt_of_ge log_32e12_lt

/--
info: 'Hex.Interval.Experiment.PntLogRational.log_2_353_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntLogRational.log_2_353_gt

/--
info: 'Hex.Interval.Experiment.PntLogRational.log_3e10_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntLogRational.log_3e10_lt

/-! ## Generic proof emission and ordinary theorem closure -/

private def inputExpr (value : Input) : Expr :=
  mkApp3 (mkConst ``Input.mk) (mkNatLit value.sourceIndex)
    (mkNatLit value.numerator) (mkNatLit value.denominator)
private def windowExpr (value : Window) : Expr :=
  mkApp4 (mkConst ``Window.mk) (mkNatLit value.sourceIndex) (mkNatLit value.lower)
    (mkNatLit value.upper) (mkNatLit value.scale)
private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .exact value => mkApp (mkConst ``Bound.exact) (inputExpr value)
  | .window value => mkApp (mkConst ``Bound.window) (windowExpr value)
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
    | throwError "pnt_log_rational: search or registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_log_rational: chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "pnt_log_rational: expected one rule event"
  unless step.entry.replayKey == factSchema.key &&
      step.entry.body == encode row32e12 &&
      step.assumptions == [{ node := node 0, fact := .exact row32e12.input }] do
    throwError "pnt_log_rational: emitted row drifted"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact representativeInput.target

/-- Representative ordinary-kernel theorem emitted through generic checked replay. -/
theorem pntLog32e12 :
    (31.0967570 : ℝ) < Real.log 32e12 ∧ Real.log 32e12 < 31.0967571 := by
  run_tac
    let evidence ← emitEvidence
    let proof ← mkAppM ``closeLog32e12 #[evidence]
    let goal ← getMainGoal
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "pnt_log_rational: closed replay has the wrong theorem"
    goal.assign (← instantiateMVars proof)
    replaceMainGoal []

/--
info: 'Hex.IntervalMathlib.PntLogRationalConformance.pntLog32e12' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntLog32e12

end Hex.IntervalMathlib.PntLogRationalConformance
