/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntLogTable
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ logarithm acceptance probe

This fixture covers `LogTables.log_2_gt` and `LogTables.log_2_lt` from PNT+
commit `21998bb6196b56789f72a52656a781a75e134eb0`.  Search runs the ordinary
Mathlib-free watched-input package.  Proof emission replays its one-event
chronology through the package schema and closes the original real theorem.
-/

namespace Hex.IntervalMathlib.PntLogTableConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntLogTable

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

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
  some
    { session := result.session
      registry
      reached
      events := result.events }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .logTwoWindow && fixture.events.size == 1 &&
      fixture.session.state.engine.facts == #[.two, .logTwoWindow] &&
      fixture.session.state.engine.chronology == #[.fact 0] &&
      fixture.registry.emit.find? logFactSchema.key == some ``logFactSchema

#guard
  baseFacts ==
      [{ node := node 0, fact := .two }, { node := node 1, fact := .all }] &&
    checkerInput.initialFacts == #[.two, .all]

private def unknownInput : CheckerInput Bound :=
  { checkerInput with initialFacts := #[.all, .all] }

-- The executable package must not produce a numerical window without the
-- exact-input fact used by its theorem schema.
#guard
  (run? unknownInput).any fun result =>
    match result.stop with
    | .saturated =>
        result.events.size == 1 &&
          result.session.state.engine.facts == #[.all, .all] &&
          result.session.state.engine.chronology.isEmpty
    | _ => false

private def offsetInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }

private def offsetProgram : Program :=
  { operations
    nodes := #[sourceInstruction, sourceInstruction, offsetInstruction] }

private def offsetInput : CheckerInput Bound :=
  { baseProgram := offsetProgram
    initialFacts := #[.two, .all, .all]
    target := { node := node 2, fact := .logTwoWindow } }

-- The same package route is not tied to node one of the two-node fixture.
#guard
  (run? offsetInput).any fun result =>
    match result.stop with
    | .target reached =>
        reached.seen == ({ node := node 2, version := 1 } : SeenVersion) &&
          reached.fact == .logTwoWindow && result.events.size == 1 &&
          result.session.state.engine.facts ==
            #[.two, .all, .logTwoWindow]
    | _ => false

private def offsetAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := logRuleKey
    node := node 2
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node 2] }

private def offsetContext : RuleFactContext offsetInput offsetAction :=
  { program := offsetProgram
    basePrefix := ProgramPrefix.refl offsetProgram
    assumptions := [{ node := node 0, fact := .two }]
    proposed := { node := node 2, fact := .logTwoWindow } }

#guard
  (logFactSchema.replay offsetInput offsetAction offsetContext ()).isSome

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
          step.entry.replayKey == logFactSchema.key &&
            step.event.programVersion == 0 && step.event.node == node 1 &&
            step.event.previous == ({ node := node 1, version := 0 } : SeenVersion) &&
            step.event.fact == .logTwoWindow && step.event.version == 1 &&
            step.assumptions == [{ node := node 0, fact := .two }] &&
            step.previous == .all
      | _ => false

/-! ## Replay mutation rejection -/

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := logRuleKey
    node := node 1
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node 1] }

private def replayContext : RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := [{ node := node 0, fact := .two }]
    proposed := { node := node 1, fact := .logTwoWindow } }

#guard (logFactSchema.decode [Bound.logTwoWindow.code]).isSome
#guard (logFactSchema.decode [Bound.all.code]).isNone
#guard factFormat.validateBody [Bound.logTwoWindow.code]
#guard !factFormat.validateBody [Bound.logTwoWindow.code, 99]
#guard (logFactSchema.replay checkerInput action replayContext ()).isSome

private def wrongInput : RuleFactContext checkerInput action :=
  { replayContext with assumptions := [{ node := node 0, fact := .all }] }

private def wrongOutput : RuleFactContext checkerInput action :=
  { replayContext with proposed := { node := node 0, fact := .logTwoWindow } }

private def wrongFact : RuleFactContext checkerInput action :=
  { replayContext with proposed := { node := node 1, fact := .all } }

#guard (logFactSchema.replay checkerInput action wrongInput ()).isNone
#guard (logFactSchema.replay checkerInput action wrongOutput ()).isNone
#guard (logFactSchema.replay checkerInput action wrongFact ()).isNone

/-! ## Generic proof emission and ordinary theorem closure -/

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .two => mkConst ``Bound.two
  | .logTwoWindow => mkConst ``Bound.logTwoWindow
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
    | throwError "pnt_log_table: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_log_table: chronology quotation failed"
  unless trace.program == program do
    throwError "pnt_log_table: trace changed the expression graph"
  let [.rule step] := trace.events
    | throwError "pnt_log_table: expected exactly one rule event"
  unless step.entry.replayKey == logFactSchema.key &&
      step.assumptions == [{ node := node 0, fact := .two }] &&
      step.event.node == node 1 && step.event.fact == .logTwoWindow do
    throwError "pnt_log_table: emitted event drifted from the pinned probe"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact
    checkerInput.target

/-- The two pinned PNT+ `log 2` bounds, proved by generic Hex planning and
schema replay and closed as an ordinary kernel theorem. -/
theorem pntLogTwo :
    (0.693147 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.693148 := by
  run_tac
    let evidence ← emitEvidence
    let proof ← mkAppM ``closeLogTwo #[evidence]
    let goal ← getMainGoal
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "pnt_log_table: closed replay has the wrong theorem"
    goal.assign (← instantiateMVars proof)
    replaceMainGoal []

/--
info: 'Hex.IntervalMathlib.PntLogTableConformance.pntLogTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntLogTwo

end Hex.IntervalMathlib.PntLogTableConformance
