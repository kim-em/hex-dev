/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntNestedLog
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ nested-logarithm acceptance probe

This fixture covers inventory record 404, declaration
`LogTables.log_log_6_58_gt`, from PNT+ commit
`21998bb6196b56789f72a52656a781a75e134eb0`.  Search applies one ordinary
Mathlib-free log package twice.  Replay first checks a positive enclosure for
`log 6.58`, then consumes that exact dependency to close the outer logarithm.
-/

namespace Hex.IntervalMathlib.PntNestedLogConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntNestedLog

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
  some { session := result.session, registry, reached, events := result.events }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 2, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .nestedLower && fixture.events.size == 2 &&
      fixture.session.state.engine.facts ==
        #[.six58, .innerWindow, .nestedLower] &&
      fixture.session.state.engine.chronology == #[.fact 0, .fact 1] &&
      fixture.registry.emit.find? logFactSchema.key == some ``logFactSchema

#guard
  baseFacts ==
      [{ node := node 0, fact := .six58 },
        { node := node 1, fact := .all },
        { node := node 2, fact := .all }] &&
    checkerInput.initialFacts == #[.six58, .all, .all]

private def offsetInner : Node :=
  { domain := real, op := { index := 1 }, args := [node 1] }

private def offsetOuter : Node :=
  { domain := real, op := { index := 1 }, args := [node 2] }

private def offsetProgram : Program :=
  { operations
    nodes := #[sourceInstruction, sourceInstruction, offsetInner, offsetOuter] }

private def offsetInput : CheckerInput Bound :=
  { baseProgram := offsetProgram
    initialFacts := #[.all, .six58, .all, .all]
    target := { node := node 3, fact := .nestedLower } }

-- The two-stage package route is independent of the fixture's node positions.
#guard
  (run? offsetInput).any fun result =>
    match result.stop with
    | .target reached =>
        reached.seen == ({ node := node 3, version := 1 } : SeenVersion) &&
          reached.fact == .nestedLower && result.events.size == 2 &&
          result.session.state.engine.facts ==
            #[.all, .six58, .innerWindow, .nestedLower] &&
          result.session.state.engine.chronology == #[.fact 0, .fact 1]
    | _ => false

private def zeroTouchingInput : CheckerInput Bound :=
  { checkerInput with initialFacts := #[.all, .zeroTouchingInner, .all] }

-- An inner enclosure that includes zero is not a valid log domain.  The
-- planner reports domain-unknown as saturation, rather than fabricating an
-- outer bound.  Dropping `.six58` is deliberate: retaining it would let the
-- first rule refine the mutated inner fact back to `.innerWindow`, obscuring
-- the outer rule's domain rejection.
#guard
  (run? zeroTouchingInput).any fun result =>
    match result.stop with
    | .saturated =>
        result.session.state.engine.facts ==
          #[.all, .zeroTouchingInner, .all] &&
          result.session.state.engine.chronology.isEmpty
    | _ => false

def trace? : Option (Frontend.Trace Bound) :=
  match fixture? with
  | none => none
  | some fixture =>
      Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program &&
      match trace.events with
      | [.rule inner, .rule outer] =>
          inner.entry.replayKey == logFactSchema.key &&
            inner.event.node == node 1 && inner.event.fact == .innerWindow &&
            inner.assumptions == [{ node := node 0, fact := .six58 }] &&
            inner.previous == .all &&
          outer.entry.replayKey == logFactSchema.key &&
            outer.event.node == node 2 && outer.event.fact == .nestedLower &&
            outer.assumptions == [{ node := node 1, fact := .innerWindow }] &&
            outer.previous == .all
      | _ => false

/-! ## Replay mutation rejection -/

private def innerAction : Action :=
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

private def innerContext : RuleFactContext checkerInput innerAction :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := [{ node := node 0, fact := .six58 }]
    proposed := { node := node 1, fact := .innerWindow } }

private def outerAction : Action :=
  { serial := 1
    programVersion := 0
    application := { index := 1 }
    rule := { index := 0 }
    key := logRuleKey
    node := node 2
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node 2] }

private def outerContext : RuleFactContext checkerInput outerAction :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := [{ node := node 1, fact := .innerWindow }]
    proposed := { node := node 2, fact := .nestedLower } }

private def wrongInnerSource : RuleFactContext checkerInput innerAction :=
  { innerContext with assumptions := [{ node := node 0, fact := .all }] }

#guard (logFactSchema.decode [Bound.innerWindow.code]).isSome
#guard (logFactSchema.decode [Bound.nestedLower.code]).isSome
#guard (logFactSchema.decode [Bound.zeroTouchingInner.code]).isNone
#guard factFormat.validateBody [Bound.innerWindow.code]
#guard factFormat.validateBody [Bound.nestedLower.code]
#guard !factFormat.validateBody [Bound.nestedLower.code, 99]
#guard (logFactSchema.replay checkerInput innerAction innerContext .innerWindow).isSome
#guard (logFactSchema.replay checkerInput outerAction outerContext .nestedLower).isSome
#guard
  (logFactSchema.replay checkerInput innerAction wrongInnerSource
    .innerWindow).isNone

private def zeroTouchingContext : RuleFactContext checkerInput outerAction :=
  { outerContext with
    assumptions := [{ node := node 1, fact := .zeroTouchingInner }] }

private def bypassedInnerContext : RuleFactContext checkerInput outerAction :=
  { outerContext with assumptions := [{ node := node 0, fact := .six58 }] }

private def wrongOuterFact : RuleFactContext checkerInput outerAction :=
  { outerContext with proposed := { node := node 2, fact := .innerWindow } }

private def wrongOuterNode : RuleFactContext checkerInput outerAction :=
  { outerContext with proposed := { node := node 0, fact := .nestedLower } }

-- Both the semantic schema and executable planner reject the zero-containing
-- mutation.  The outer proof cannot bypass the first replay stage by reading
-- the original source point directly.
#guard
  (logFactSchema.replay checkerInput outerAction zeroTouchingContext
    .nestedLower).isNone
#guard
  (logFactSchema.replay checkerInput outerAction bypassedInnerContext
    .nestedLower).isNone
#guard
  (logFactSchema.replay checkerInput outerAction wrongOuterFact
    .nestedLower).isNone
#guard
  (logFactSchema.replay checkerInput outerAction wrongOuterNode
    .nestedLower).isNone

/-! ## Generic proof emission and ordinary theorem closure -/

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .six58 => mkConst ``Bound.six58
  | .innerWindow => mkConst ``Bound.innerWindow
  | .zeroTouchingInner => mkConst ``Bound.zeroTouchingInner
  | .nestedLower => mkConst ``Bound.nestedLower
  | .positiveSlice => mkConst ``Bound.positiveSlice
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
    | throwError "pnt_nested_log: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_nested_log: chronology quotation failed"
  unless trace.program == program do
    throwError "pnt_nested_log: trace changed the expression graph"
  let [.rule inner, .rule outer] := trace.events
    | throwError "pnt_nested_log: expected exactly two rule events"
  unless inner.entry.replayKey == logFactSchema.key &&
      inner.assumptions == [{ node := node 0, fact := .six58 }] &&
      inner.event.node == node 1 && inner.event.fact == .innerWindow &&
      outer.entry.replayKey == logFactSchema.key &&
      outer.assumptions == [{ node := node 1, fact := .innerWindow }] &&
      outer.event.node == node 2 && outer.event.fact == .nestedLower do
    throwError "pnt_nested_log: emitted dependency chain drifted"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target

/-- PNT+ `LogTables.log_log_6_58_gt`, proved through two generic Hex planning
and replay events and closed as an ordinary kernel theorem. -/
theorem pntNestedLog :
    (0.633415 : ℝ) < Real.log (Real.log 6.58) := by
  run_tac
    let evidence ← emitEvidence
    let proof ← mkAppM ``closeNestedLog #[evidence]
    let goal ← getMainGoal
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "pnt_nested_log: closed replay has the wrong theorem"
    goal.assign (← instantiateMVars proof)
    replaceMainGoal []

/--
info: 'Hex.IntervalMathlib.PntNestedLogConformance.pntNestedLog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntNestedLog

end Hex.IntervalMathlib.PntNestedLogConformance
