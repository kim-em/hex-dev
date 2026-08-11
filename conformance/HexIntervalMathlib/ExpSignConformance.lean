/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.ExpSign
import HexInterval.Experiment.GoalFrontend
import HexInterval.Experiment.ProofFrontend
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Exponential package and generic frontend conformance

This is the second mathematical-function client of the interval framework.
It uses a different fact type, no instantiation, no equality transport, and an
unconditional `Real.exp` propagator.  The same joint package registry,
chronology quotation, structural encoder, and dependent proof fold produce an
ordinary kernel-checked theorem.
-/

namespace Hex.IntervalMathlib.ExpSignConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend FrontendEncoder ProofFrontend ProofRegistry GoalFrontend ExpSign

/-! ## Extensible goal reification -/

private def sourceSyntax : GoalFrontend.Package :=
  { operation := sourceOperation
    recognize := fun expression => do
      let type ← inferType expression
      pure <|
        if expression.isFVar && type == mkConst ``Real then some [] else none }

private def expSyntax : GoalFrontend.Package :=
  { operation := expOperation
    recognize := fun expression =>
      let arguments := expression.getAppArgs
      pure <|
        if expression.getAppFn.constName? == some ``Real.exp &&
            arguments.size == 1 then
          some [arguments[0]!]
        else
          none }

private def goalRegistry? : Except String GoalFrontend.Registry :=
  GoalFrontend.Registry.build
    { maxPackages := 4, maxNodes := 16, maxDepth := 8 }
    #[sourceSyntax, expSyntax]

private def isZero (expression : Expr) : Bool :=
  let arguments := expression.getAppArgs
  expression.getAppFn.constName? == some ``OfNat.ofNat &&
    arguments.size == 3 &&
      match arguments[1]! with
      | .lit (.natVal 0) => true
      | _ => false

private def claimParser : GoalFrontend.Parser Bound :=
  { parse := fun proposition =>
      let arguments := proposition.getAppArgs
      if proposition.getAppFn.constName? == some ``LE.le &&
          arguments.size ≥ 2 then
        let left := arguments[arguments.size - 2]!
        let right := arguments[arguments.size - 1]!
        if isZero left then
          pure <| some
            { expression := right
              domain := real
              fact := .nonnegative }
        else
          pure none
      else
        pure none }

private meta def reifyGoal (target : Expr) : MetaM (GoalFrontend.Result Bound) := do
  let registry ←
    match goalRegistry? with
    | .ok registry => pure registry
    | .error message =>
        throwError "interval_exp: invalid goal registry: {message}"
  let context ← getLCtx
  let mut hypotheses := []
  for declaration in context do
    unless declaration.isImplementationDetail do
      hypotheses := hypotheses.concat
        (← instantiateMVars declaration.type, mkFVar declaration.fvarId)
  GoalFrontend.reify registry factDomain claimParser hypotheses target

private def sameInput (input : CheckerInput Bound) : Bool :=
  input.baseProgram == checkerInput.baseProgram &&
    input.initialFacts == checkerInput.initialFacts &&
    input.target == checkerInput.target

def offer? (session : PolicySession.Session Bound)
    (accepts : Propagator.Policy.OfferView → Bool) :
    Option
      (Propagator.Policy.OfferView × Propagator.Policy.Selection ×
        PolicySession.Session Bound) :=
  match session.view with
  | .ready view viewed =>
      match view.offers.toList.find? accepts with
      | none => none
      | some offer =>
          some
            (offer,
              { scope := view.scope
                serial := view.serial
                programVersion := view.programVersion
                id := offer.id
                expected := offer.key },
              viewed)
  | .resource _ _ | .contradiction _ | .invalidSession _ => none

def invokesExp (offer : Propagator.Policy.OfferView) : Bool :=
  match offer.key with
  | .invoke invocation =>
      invocation.rule == expRuleKey && invocation.anchor == node 1
  | _ => false

def contracted? : Option (PolicySession.Session Bound) := do
  let .ok session := start | none
  let (_, selection, viewed) ← offer? session invokesExp
  match viewed.choose (.select selection) with
  | .rule _ observation next =>
      if observation.outcome == .success then some next else none
  | _ => none

#guard
  contracted?.any fun session =>
    session.live && !session.droppedWork &&
      session.state.engine.program == program &&
      session.state.engine.facts[1]? == some .nonnegative &&
      session.state.engine.history.size == 1 &&
      session.state.engine.instanceHistory.isEmpty &&
      session.state.engine.equalities.isEmpty &&
      session.state.engine.chronology == #[.fact 0]

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name

def fixture? : Option Fixture := do
  let session ← contracted?
  match ProofRegistry.build session.registry proofPackages with
  | .ok registry => some { session, registry }
  | .error _ => none

#guard
  fixture?.any fun fixture =>
    fixture.registry.emit.find? expFactSchema.key == some ``expFactSchema

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
          step.entry.replayKey == expFactSchema.key &&
            step.event.node == node 1 &&
            step.event.fact == .nonnegative
      | _ => false

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .nonnegative => mkConst ``Bound.nonnegative
  | .empty => mkConst ``Bound.empty

private def seedAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence (semantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def frontendContext : ProofFrontend.Context Bound Name :=
  { encoder := FrontendEncoder.make (mkConst ``Bound)
      (fun fact => pure (boundExpr fact))
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
    | throwError "interval_exp: compiled search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "interval_exp: chronology quotation failed"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  let target := { node := node 1, version := 1 : SeenVersion }
  let some proof := ProofFrontend.findProof? state.known target .nonnegative
    | throwError "interval_exp: target fact was not emitted"
  pure proof

private def expTarget (x : ℝ) : Prop :=
  0 ≤ Real.exp x

private meta def proveExp (target : Expr) : MetaM Expr := do
  let reified ← reifyGoal target
  unless sameInput reified.input do
    throwError "interval_exp: goal reification produced an unexpected checker input"
  let context ← getLCtx
  for declaration in context do
    unless declaration.isImplementationDetail do
      let saved ← saveState
      let candidate? ← observing? <|
        mkAppM ``expTarget #[mkFVar declaration.fvarId]
      match candidate? with
      | some candidate =>
          if ← isDefEq candidate target then
            let evidence ← emitEvidence
            let proof ←
              mkAppM ``closeExp #[mkFVar declaration.fvarId, evidence]
            unless ← isDefEq (← inferType proof) target do
              throwError "interval_exp: emitted replay has the wrong target"
            return (← instantiateMVars proof)
          saved.restore
      | none => saved.restore
  throwError "interval_exp: expected a goal definitionally equal to `0 ≤ Real.exp x`"

syntax (name := intervalExpTac) "interval_exp" : tactic

@[tactic intervalExpTac] meta def evalIntervalExp : Tactic := fun stx => do
  match stx with
  | `(tactic| interval_exp) =>
      let goal ← getMainGoal
      goal.withContext do
        let proof ← proveExp (← instantiateMVars (← goal.getType))
        goal.assign proof
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

theorem tacticExp (x : ℝ) : 0 ≤ Real.exp x := by
  interval_exp

example (_x : ℝ) : True := by
  fail_if_success interval_exp
  trivial

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example (x : ℝ) (h : 0 ≤ Real.exp x) : True := by
  run_tac
    let context ← getLCtx
    let mut target? := none
    for declaration in context do
      if (← claimParser.parse declaration.type).isSome then
        target? := some declaration.type
    let some target := target?
      | throwError "interval_exp goal test: parsed hypothesis is missing"
    let result ← reifyGoal target
    let some seed := result.seeds[1]?
      | throwError "interval_exp goal test: target seed is missing"
    unless result.input.baseProgram.nodes.size == 2 &&
        result.terms.size == 2 && seed.assumptions.length == 1 &&
        result.input.initialFacts[1]? == some .nonnegative do
      throwError "interval_exp goal test: CSE or assumption seeding failed"
    let aliasPackage : GoalFrontend.Package :=
      { expSyntax with
        operation :=
          { expOperation with key := { name := "exp-sign.exp-alias" } } }
    let registry ←
      match GoalFrontend.Registry.build
          { maxPackages := 4, maxNodes := 16, maxDepth := 8 }
          #[sourceSyntax, expSyntax, aliasPackage] with
      | .ok registry => pure registry
      | .error message =>
          throwError "interval_exp goal test: invalid alias registry: {message}"
    if (← observing? <|
        GoalFrontend.reify registry factDomain claimParser [] target).isSome then
      throwError "interval_exp goal test: ambiguous syntax packages were accepted"
  trivial

set_option linter.unusedTactic false in
example : True := by
  run_tac
    let some fixture := fixture?
      | throwError "interval_exp test: missing live fixture"
    let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
      | throwError "interval_exp test: missing trace"
    let [.rule step] := trace.events
      | throwError "interval_exp test: wrong event shape"
    let stale : RuleStep Bound :=
      { step with event := { step.event with programVersion := 1 } }
    if (← observing? (ProofFrontend.emitTrace frontendContext program
        [.rule stale] fixture.registry.emit)).isSome then
      throwError "interval_exp test: stale rule version was accepted"
  trivial

end Hex.IntervalMathlib.ExpSignConformance
