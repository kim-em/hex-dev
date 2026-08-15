/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.MixedFunctions
import HexInterval.Experiment.GoalFrontend
import HexInterval.Experiment.GoalClosure
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Mixed sine/exponential tactic conformance

One generic goal reifier selects three independently registered syntax
packages for `x`, `Real.sin x`, and `Real.exp (Real.sin x)`.  Search first
replays sine's unit-range theorem, then exponential's upper-bound theorem.
The generic scheduler and proof frontend contain no cases for either function.
-/

namespace Hex.IntervalMathlib.MixedFunctionsConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend FrontendEncoder ProofFrontend ProofRegistry GoalFrontend GoalClosure
open MixedFunctions

private def sourceSyntax : GoalFrontend.Package :=
  { operation := sourceOperation
    recognize := fun expression => do
      let type ← inferType expression
      pure <|
        if expression.isFVar && type == mkConst ``Real then some [] else none }

private def sineSyntax : GoalFrontend.Package :=
  { operation := sineOperation
    recognize := fun expression =>
      let arguments := expression.getAppArgs
      pure <|
        if expression.getAppFn.constName? == some ``Real.sin &&
            arguments.size == 1 then
          some [arguments[0]!]
        else none }

private def expSyntax : GoalFrontend.Package :=
  { operation := expOperation
    recognize := fun expression =>
      let arguments := expression.getAppArgs
      pure <|
        if expression.getAppFn.constName? == some ``Real.exp &&
            arguments.size == 1 then
          some [arguments[0]!]
        else none }

private def goalRegistry? : Except String GoalFrontend.Registry :=
  GoalFrontend.Registry.build
    { maxPackages := 4, maxNodes := 16, maxDepth := 8 }
    #[sourceSyntax, sineSyntax, expSyntax]

private def isThree (expression : Expr) : Bool :=
  let arguments := expression.getAppArgs
  expression.getAppFn.constName? == some ``OfNat.ofNat &&
    arguments.size == 3 &&
      match arguments[1]! with
      | .lit (.natVal 3) => true
      | _ => false

private def claimParser : GoalFrontend.Parser Bound :=
  { parse := fun proposition => do
      let arguments := proposition.getAppArgs
      if proposition.getAppFn.constName? == some ``LE.le &&
          arguments.size ≥ 2 then
        let left := arguments[arguments.size - 2]!
        let right := arguments[arguments.size - 1]!
        let leftType ← inferType left
        if isThree right && leftType == mkConst ``Real then
          pure <| some
            { expression := left
              domain := real
              fact := .atMostThree }
        else pure none
      else pure none }

private theorem sourceAligned : sourceModel.operation = sourceOperation := rfl
private theorem sineAligned : sineModel.operation = sineOperation := rfl
private theorem expAligned : expModel.operation = expOperation := rfl

private def sourceMeaning : GoalClosure.Package :=
  { operation := sourceOperation
    model := mkConst ``sourceModel
    aligned := mkConst ``sourceAligned
    prove := fun arguments _ => do
      unless arguments.isEmpty do
        throwError "interval_mixed: source meaning received arguments"
      mkAppM ``Eq.refl #[FrontendEncoder.listExpr (mkConst ``Real) []] }

private def sineMeaning : GoalClosure.Package :=
  { operation := sineOperation
    model := mkConst ``sineModel
    aligned := mkConst ``sineAligned
    prove := fun arguments output => do
      let [input] := arguments
        | throwError "interval_mixed: sine meaning is not unary"
      let expected ← mkAppM ``Real.sin #[input]
      unless ← isDefEq output expected do
        throwError "interval_mixed: sine recognizer changed the expression"
      mkAppM ``Eq.refl #[output] }

private def expMeaning : GoalClosure.Package :=
  { operation := expOperation
    model := mkConst ``expModel
    aligned := mkConst ``expAligned
    prove := fun arguments output => do
      let [input] := arguments
        | throwError "interval_mixed: exponential meaning is not unary"
      let expected ← mkAppM ``Real.exp #[input]
      unless ← isDefEq output expected do
        throwError "interval_mixed: exponential recognizer changed the expression"
      mkAppM ``Eq.refl #[output] }

private def meanings : Array GoalClosure.Package :=
  #[sourceMeaning, sineMeaning, expMeaning]

private meta def reifyGoal (target : Expr) : MetaM (GoalFrontend.Result Bound) := do
  let registry ←
    match goalRegistry? with
    | .ok registry => pure registry
    | .error message => throwError "interval_mixed: invalid registry: {message}"
  let context ← getLCtx
  let mut hypotheses := []
  for declaration in context do
    unless declaration.isImplementationDetail do
      hypotheses := hypotheses.concat
        (← instantiateMVars declaration.type, mkFVar declaration.fvarId)
  GoalFrontend.reify registry factDomain claimParser hypotheses target

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private structure Fixture where
  result : TargetRun.Result Bound Unit
  reached : TargetRun.Reached Bound
  registry : ProofRegistry.Registry semantics Name

private def runInput? (input : CheckerInput Bound) : Option Fixture := do
  let .ok session := PolicySession.Session.start factDomain input.baseProgram
      packages input.initialFacts limits
    | none
  let result := TargetRun.drive factDomain input.target.node input.target.fact
    firstOffer limits.policy.maxDecisions session ()
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { result, reached, registry }

private def node (index : Nat) : NodeId := { index }

private def mixedProgram : Program :=
  { operations
    nodes :=
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 1 }, args := [node 0] },
        { domain := real, op := { index := 2 }, args := [node 1] }] }

private def mixedInput : CheckerInput Bound :=
  { baseProgram := mixedProgram
    initialFacts := #[.all, .all, .all]
    target := { node := node 2, fact := .atMostThree } }

private def mixedView : ProgramView :=
  { programVersion := 0
    operations
    nodes := mixedProgram.nodes
    generations := #[0, 0, 0]
    depths := #[0, 1, 2] }

private def expAction : Action :=
  { serial := 1
    programVersion := 0
    application := { index := 1 }
    rule := { index := 1 }
    key := expRuleKey
    node := node 2
    kind := .forward
    effort := 0
    inputs := [{ node := node 1, version := 1 }]
    writes := [node 2] }

private def expRequest (fact : Bound) (version : Nat) : RuleRequest Bound :=
  { action := { expAction with inputs := [{ node := node 1, version }] }
    program := mixedView
    inputs := [{ node := node 1, fact, version }]
    writes := [node 2] }

/- The exponential callback is unavailable at the initial top fact and becomes
applicable only after the exact sine fact has been installed. -/
#guard
  match (expPlan (expRequest .all 0)).outcome with
  | .failed 2 => true
  | _ => false

#guard
  match (expPlan (expRequest .unit 1)).outcome with
  | .success [candidate] [] _ =>
      candidate.node == node 2 && candidate.fact == .atMostThree
  | _ => false

private def expContext : RuleFactContext mixedInput expAction :=
  { program := mixedProgram
    basePrefix := ProgramPrefix.refl mixedProgram
    assumptions := [{ node := node 1, fact := .unit }]
    proposed := { node := node 2, fact := .atMostThree } }

private def wrongExpFact : RuleFactContext mixedInput expAction :=
  { expContext with assumptions := [{ node := node 1, fact := .all }] }

private def bypassedSine : RuleFactContext mixedInput expAction :=
  { expContext with assumptions := [{ node := node 0, fact := .unit }] }

#guard (expFactSchema.replay mixedInput expAction expContext ()).isSome
#guard (expFactSchema.replay mixedInput expAction wrongExpFact ()).isNone
#guard (expFactSchema.replay mixedInput expAction bypassedSine ()).isNone

private structure MixedSummary where
  reached : SeenVersion
  fact : Bound
  facts : Array Bound
  chronology : Array HistoryEvent

private def mixedSummary? : Option MixedSummary := do
  let .ok session := PolicySession.Session.start factDomain mixedProgram
      packages mixedInput.initialFacts limits
    | none
  let result := TargetRun.drive factDomain mixedInput.target.node
    mixedInput.target.fact firstOffer limits.policy.maxDecisions session ()
  let .target reached := result.stop | none
  some
    { reached := reached.seen
      fact := reached.fact
      facts := result.session.state.engine.facts
      chronology := result.session.state.engine.chronology }

#guard
  mixedSummary?.any fun summary =>
    summary.reached == ({ node := node 2, version := 1 } : SeenVersion) &&
      summary.fact == .atMostThree &&
      summary.facts == #[.all, .unit, .atMostThree] &&
      summary.chronology == #[.fact 0, .fact 1]

private def mixedTrace? : Option (Frontend.Trace Bound) := do
  let .ok session := PolicySession.Session.start factDomain mixedProgram
      packages mixedInput.initialFacts limits
    | none
  let result := TargetRun.drive factDomain mixedInput.target.node
    mixedInput.target.fact firstOffer limits.policy.maxDecisions session ()
  let .target _ := result.stop | none
  Frontend.trace? result.session.state.engine result.session.arena

#guard
  mixedTrace?.any fun trace =>
    match trace.events with
    | [.rule sine, .rule exp] =>
        sine.entry.replayKey == sineFactSchema.key &&
          sine.assumptions == [{ node := node 0, fact := .all }] &&
          exp.entry.replayKey == expFactSchema.key &&
          exp.assumptions == [{ node := node 1, fact := .unit }]
    | _ => false

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .unit => mkConst ``Bound.unit
  | .atMostThree => mkConst ``Bound.atMostThree
  | .empty => mkConst ``Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))

private def factBridge : GoalClosure.FactBridge Bound :=
  { runtime := factDomain
    schema := mkConst ``boundSchema
    proveAssumption := fun program valuation node fact _ proof => do
      let expected ←
        mkAppM ``SemanticReplay.Semantics.holds
          #[mkConst ``semantics, program, valuation,
            ← boundEncoder.nodeFact { node, fact }]
      unless ← isDefEq (← inferType proof) expected do
        throwError "interval_mixed: hypothesis does not prove its parsed fact"
      pure proof }

private def seedAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence (semantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def inputContext (result : GoalFrontend.Result Bound)
    (base : GoalClosure.BaseProof) : ProofFrontend.Context Bound Name :=
  { encoder := boundEncoder
    resolveSchema := pure
    semantics := mkConst ``semantics
    domain := mkConst ``boundSchema
    laws := mkConst ``laws
    stableLaw := mkConst ``stableLaw
    input := base.input
    assumed := ``seedAssumed
    baseFacts := result.baseFacts
    baseFactsTerm := base.facts
    baseProgram := result.input.baseProgram
    baseProgramTerm := base.program
    basePrefix := base.basePrefix
    baseWithin := base.within
    initialExtension := base.extension
    finalPrefix := base.basePrefix
    sameOperations := base.sameOperations
    top := boundSchema.top }

private meta def emitInput (result : GoalFrontend.Result Bound)
    (base : GoalClosure.BaseProof) : MetaM Expr := do
  let some fixture := runInput? result.input
    | throwError "interval_mixed: search or proof registry failed"
  let some trace := Frontend.trace? fixture.result.session.state.engine
      fixture.result.session.arena
    | throwError "interval_mixed: chronology quotation failed"
  unless trace.program == result.input.baseProgram do
    throwError "interval_mixed: propagation unexpectedly changed the graph"
  let state ← ProofFrontend.emitTrace (inputContext result base)
    trace.program trace.events fixture.registry.emit
  ProofFrontend.closeTarget (inputContext result base) state fixture.reached.seen
    fixture.reached.fact result.input.target

private meta def proveMixed (target : Expr) : MetaM Expr := do
  let result ← reifyGoal target
  unless result.input.baseProgram.operations == operations &&
      result.input.baseProgram.nodes.size == 3 &&
      result.input.target.node == ({ index := 2 } : NodeId) do
    throwError "interval_mixed: reifier produced an unexpected graph"
  let some fallback := GoalClosure.termAt? result.terms { index := 0 }
    | throwError "interval_mixed: source expression is missing"
  let model ← GoalClosure.proveModel (mkConst ``Real) fallback meanings
    boundEncoder result
  let base ← GoalClosure.proveBase (mkConst ``Bound) (mkConst ``semantics)
    boundEncoder result.input
  let facts ← GoalClosure.proveFacts factBridge boundEncoder result base model
  let evidence ← emitInput result base
  let proof ←
    mkAppM ``Evidence.proof #[evidence, model.valuation, model.proof, facts]
  unless ← isDefEq (← inferType proof) target do
    throwError "interval_mixed: emitted proof has the wrong target"
  pure (← instantiateMVars proof)

syntax (name := intervalMixedTac) "interval_mixed" : tactic

@[tactic intervalMixedTac] meta def evalIntervalMixed : Tactic := fun stx => do
  match stx with
  | `(tactic| interval_mixed) =>
      let goal ← getMainGoal
      goal.withContext do
        goal.assign (← proveMixed (← instantiateMVars (← goal.getType)))
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

/-- Both arbitrary-function packages contribute a replayed fact, and the
exponential proof consumes the sine proof as its exact dependency. -/
theorem mixedSinExp (x : ℝ) : Real.exp (Real.sin x) ≤ 3 := by
  interval_mixed

/--
info: 'Hex.IntervalMathlib.MixedFunctionsConformance.mixedSinExp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mixedSinExp

example (_x : ℝ) : True := by
  fail_if_success interval_mixed
  trivial

end Hex.IntervalMathlib.MixedFunctionsConformance
