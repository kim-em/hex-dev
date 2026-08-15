/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntNestedLogTwo
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ two-sided nested log

Two generic log events prove both remaining `log (log 2)` declarations: the
first checks a strict positive `log 2` enclosure and the second consumes both
of its endpoints.
-/

namespace Hex.IntervalMathlib.PntNestedLogTwoConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntNestedLogTwo

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view => match view.offers[0]? with
      | some offer => .select offer state | none => .stop state }

private def run? (input : CheckerInput Bound) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain input.baseProgram
      packages input.initialFacts limits | none
  some (TargetRun.drive factDomain input.target.node input.target.fact firstOffer
    limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name
  reached : TargetRun.Reached Bound

def fixture? : Option Fixture := do
  let result ← run? checkerInput
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { session := result.session, registry, reached }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 2, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .outerWindow &&
      fixture.session.state.engine.facts == #[.two, .innerWindow, .outerWindow] &&
      fixture.session.state.engine.chronology == #[.fact 0, .fact 1] &&
      fixture.registry.emit.find? factSchema.key == some ``factSchema

private def zeroTouchingInput : CheckerInput Bound :=
  { checkerInput with initialFacts := #[.all, .zeroTouchingInner, .all] }

-- Dropping the exact source is deliberate: otherwise the first event would
-- replace the mutation with the valid strict positive enclosure.
#guard
  (run? zeroTouchingInput).any fun result =>
    match result.stop with
    | .saturated =>
        result.session.state.engine.facts == #[.all, .zeroTouchingInner, .all] &&
          result.session.state.engine.chronology.isEmpty &&
          result.session.arena.entries.isEmpty
    | _ => false

def trace? : Option (Frontend.Trace Bound) :=
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace => trace.program == program &&
    match trace.events with
    | [.rule inner, .rule outer] =>
        inner.entry.replayKey == factSchema.key &&
          inner.entry.body == [Bound.innerWindow.code] &&
          inner.assumptions == [{ node := node 0, fact := .two }] &&
          inner.event.node == node 1 && inner.event.fact == .innerWindow &&
        outer.entry.replayKey == factSchema.key &&
          outer.entry.body == [Bound.outerWindow.code] &&
          outer.assumptions == [{ node := node 1, fact := .innerWindow }] &&
          outer.event.node == node 2 && outer.event.fact == .outerWindow
    | _ => false

/-! ## Mutation rejection -/

private def innerAction : Action :=
  { serial := 0, programVersion := 0, application := { index := 0 },
    rule := { index := 0 }, key := ruleKey, node := node 1, kind := .forward,
    effort := 0, generation := 0, inputs := [], writes := [node 1] }
private def outerAction : Action :=
  { serial := 1, programVersion := 0, application := { index := 1 },
    rule := { index := 0 }, key := ruleKey, node := node 2, kind := .forward,
    effort := 0, generation := 0, inputs := [], writes := [node 2] }
private def innerContext : RuleFactContext checkerInput innerAction :=
  { program, basePrefix := ProgramPrefix.refl program,
    assumptions := [{ node := node 0, fact := .two }],
    proposed := { node := node 1, fact := .innerWindow } }
private def outerContext : RuleFactContext checkerInput outerAction :=
  { program, basePrefix := ProgramPrefix.refl program,
    assumptions := [{ node := node 1, fact := .innerWindow }],
    proposed := { node := node 2, fact := .outerWindow } }

#guard (factSchema.decode [Bound.innerWindow.code]).isSome
#guard (factSchema.decode [Bound.outerWindow.code]).isSome
#guard (factSchema.decode [Bound.zeroTouchingInner.code]).isNone
#guard (factSchema.replay checkerInput innerAction innerContext .innerWindow).isSome
#guard (factSchema.replay checkerInput outerAction outerContext .outerWindow).isSome

private def wrongInnerSource : RuleFactContext checkerInput innerAction :=
  { innerContext with assumptions := [{ node := node 0, fact := .all }] }
private def zeroOuter : RuleFactContext checkerInput outerAction :=
  { outerContext with assumptions :=
      [{ node := node 1, fact := .zeroTouchingInner }] }
private def bypassInner : RuleFactContext checkerInput outerAction :=
  { outerContext with assumptions := [{ node := node 0, fact := .two }] }
private def wrongOuter : RuleFactContext checkerInput outerAction :=
  { outerContext with proposed := { node := node 2, fact := .innerWindow } }

#guard (factSchema.replay checkerInput innerAction wrongInnerSource .innerWindow).isNone
#guard (factSchema.replay checkerInput outerAction zeroOuter .outerWindow).isNone
#guard (factSchema.replay checkerInput outerAction bypassInner .outerWindow).isNone
#guard (factSchema.replay checkerInput outerAction wrongOuter .outerWindow).isNone

theorem rejectFalseUpper : ¬ Real.log (Real.log 2) < (-0.366513 : ℝ) := by
  exact not_lt_of_ge log_log_2_gt

/--
info: 'Hex.Interval.Experiment.PntNestedLogTwo.log_log_2_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntNestedLogTwo.log_log_2_gt

/--
info: 'Hex.Interval.Experiment.PntNestedLogTwo.log_log_2_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntNestedLogTwo.log_log_2_lt

/-! ## Generic proof emission -/

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .two => mkConst ``Bound.two
  | .innerWindow => mkConst ``Bound.innerWindow
  | .zeroTouchingInner => mkConst ``Bound.zeroTouchingInner
  | .outerWindow => mkConst ``Bound.outerWindow
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
    | throwError "pnt_nested_log_two: search or registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_nested_log_two: chronology quotation failed"
  let [.rule inner, .rule outer] := trace.events
    | throwError "pnt_nested_log_two: expected two rule events"
  unless inner.entry.replayKey == factSchema.key &&
      inner.assumptions == [{ node := node 0, fact := .two }] &&
      outer.entry.replayKey == factSchema.key &&
      outer.assumptions == [{ node := node 1, fact := .innerWindow }] do
    throwError "pnt_nested_log_two: dependency chain drifted"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target

/-- Both strict endpoints emitted through two generic checked replay events. -/
theorem pntNestedLogTwo :
    (-0.366513 : ℝ) < Real.log (Real.log 2) ∧
      Real.log (Real.log 2) < -0.366512 := by
  run_tac
    let evidence ← emitEvidence
    let proof ← mkAppM ``closeNestedLogTwo #[evidence]
    let goal ← getMainGoal
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "pnt_nested_log_two: closed replay has the wrong theorem"
    goal.assign (← instantiateMVars proof)
    replaceMainGoal []

/--
info: 'Hex.IntervalMathlib.PntNestedLogTwoConformance.pntNestedLogTwo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pntNestedLogTwo

end Hex.IntervalMathlib.PntNestedLogTwoConformance
