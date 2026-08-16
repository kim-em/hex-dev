/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntLogNatural
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ natural logarithm table

This fixture covers the lower and upper declarations for the twelve remaining
natural-number rows in PNT+ `IEANTN/LogTables.lean` at commit
`21998bb6196b56789f72a52656a781a75e134eb0`.  A single checked runtime schema
authenticates a dyadic reduction and eight-term atanh certificate for every
row.  The generic proof frontend is exercised at representative row 29.
-/

namespace Hex.IntervalMathlib.PntLogNaturalConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntLogNatural

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? (row : Certificate) : Option (TargetRun.Result Bound Unit) := do
  let input := checkerInput row
  let .ok session := PolicySession.Session.start factDomain input.baseProgram
      packages input.initialFacts limits | none
  some (TargetRun.drive factDomain input.target.node input.target.fact firstOffer
    limits.policy.maxDecisions session ())

#guard rows.length == 12
#guard rows.all Certificate.valid
#guard rows.all fun row => rowFor? row.input == some row
#guard rows.all fun row => decode? (encode row) == some row
#guard rows.all fun row => factFormat.validateBody (encode row)
#guard rows.all fun row =>
  (run? row).any fun result =>
    match result.stop with
    | .target reached =>
        reached.fact == .window row.window && result.events.size == 1 &&
          result.session.state.engine.chronology == #[.fact 0]
    | _ => false

private def unknownRow : Certificate :=
  { row29 with input := 31, xNum := 15, xDen := 47 }

-- An exact natural outside the pinned source table saturates without a draft
-- or chronological fact; the package does not extrapolate from nearby rows.
#guard
  (run? unknownRow).any fun result =>
    match result.stop with
    | .saturated => result.events.size == 1 &&
        result.session.state.engine.chronology.isEmpty
    | _ => false

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name
  reached : TargetRun.Reached Bound

def fixture? : Option Fixture := do
  let result ← run? row29
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { session := result.session, registry, reached }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .window row29.window &&
      fixture.session.state.engine.facts == #[.exact 29, .window row29.window] &&
      fixture.registry.emit.find? factSchema.key == some ``factSchema

def trace? : Option (Frontend.Trace Bound) :=
  match fixture? with
  | none => none
  | some fixture =>
      Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program &&
      match trace.events with
      | [.rule step] =>
          step.entry.replayKey == factSchema.key &&
            step.entry.body == encode row29 &&
            step.assumptions == [{ node := node 0, fact := .exact 29 }] &&
            step.event.node == node 1 &&
            step.event.fact == .window row29.window && step.previous == .all
      | _ => false

/-! ## Mutation rejection -/

private def action : Action :=
  { serial := 0, programVersion := 0, application := { index := 0 },
    rule := { index := 0 }, key := ruleKey, node := node 1, kind := .forward,
    effort := 0, generation := 0, inputs := [], writes := [node 1] }

private def replayContext : RuleFactContext representativeInput action :=
  { program, basePrefix := ProgramPrefix.refl program,
    assumptions := [{ node := node 0, fact := .exact 29 }],
    proposed := { node := node 1, fact := .window row29.window } }

private def insufficientTerms : Certificate := { row29 with terms := 7 }
private def wrongReduction : Certificate := { row29 with shift := 5 }
private def falseEndpoint : Certificate :=
  { row29 with lower := 3367296, upper := 3367297 }

#guard (decode? (encode insufficientTerms)).isNone
#guard (decode? (encode wrongReduction)).isNone
#guard (decode? (encode falseEndpoint)).isSome
#guard (factSchema.replay representativeInput action replayContext row29).isSome
#guard (factSchema.replay representativeInput action replayContext row30).isNone
#guard (factSchema.replay representativeInput action replayContext falseEndpoint).isNone

private def wrongSource : RuleFactContext representativeInput action :=
  { replayContext with assumptions := [{ node := node 0, fact := .exact 30 }] }

private def wrongWindow : RuleFactContext representativeInput action :=
  { replayContext with proposed := { node := node 1, fact := .window row30.window } }

#guard (factSchema.replay representativeInput action wrongSource row29).isNone
#guard (factSchema.replay representativeInput action wrongWindow row29).isNone

theorem rejectFalseEndpoint : ¬ (3.367296 : ℝ) < Real.log 29 := by
  intro falseLower
  linarith [log_29_lt]

/--
info: 'Hex.Interval.Experiment.PntLogNatural.log_3_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntLogNatural.log_3_gt

/--
info: 'Hex.Interval.Experiment.PntLogNatural.log_32_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntLogNatural.log_32_lt

/-! ## Generic proof emission and ordinary theorem closure -/

private def windowExpr (value : Window) : Expr :=
  mkApp4 (mkConst ``Window.mk) (mkNatLit value.input) (mkNatLit value.lower)
    (mkNatLit value.upper) (mkNatLit value.scale)

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .exact value => mkApp (mkConst ``Bound.exact) (mkNatLit value)
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
    | throwError "pnt_log_natural: search or registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_log_natural: chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "pnt_log_natural: expected one rule event"
  unless step.entry.replayKey == factSchema.key && step.entry.body == encode row29 &&
      step.assumptions == [{ node := node 0, fact := .exact 29 }] do
    throwError "pnt_log_natural: emitted row drifted"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact representativeInput.target

/-- Representative ordinary-kernel theorem produced through generic planning,
payload authentication, chronology replay, and the proof frontend. -/
theorem pntLog29 :
    (3.367295 : ℝ) < Real.log 29 ∧ Real.log 29 < 3.367296 := by
  run_tac
    let evidence ← emitEvidence
    let proof ← mkAppM ``closeLog29 #[evidence]
    let goal ← getMainGoal
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "pnt_log_natural: closed replay has the wrong theorem"
    goal.assign (← instantiateMVars proof)
    replaceMainGoal []

/--
info: 'Hex.IntervalMathlib.PntLogNaturalConformance.pntLog29' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntLog29

end Hex.IntervalMathlib.PntLogNaturalConformance
