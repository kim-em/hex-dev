/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.MixedInstantiation
import HexInterval.Experiment.GoalFrontend
import HexInterval.Experiment.GoalClosure
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Mixed-function dynamic-instantiation conformance

The actual goal reifier initially discovers only `x`, `-x`, `sin (-x)`, and
`exp (sin (-x))`. Search cannot propagate sine on the negative-shape node.
The sine package's matcher adds `sin x` and `-(sin x)`; independent sine and
negation rules establish their unit range; generic equality transport carries
that fact back to `sin (-x)`; and the exponential package consumes it.
-/

namespace Hex.IntervalMathlib.MixedInstantiationConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend FrontendEncoder ProofFrontend ProofRegistry GoalFrontend GoalClosure
open MixedInstantiation

private def sourceSyntax : GoalFrontend.Package :=
  { operation := sourceOperation
    recognize := fun expression => do
      let type ← inferType expression
      pure <|
        if expression.isFVar && type == mkConst ``Real then some [] else none }

private def negationSyntax : GoalFrontend.Package :=
  { operation := negationOperation
    recognize := fun expression =>
      let arguments := expression.getAppArgs
      pure <|
        if expression.getAppFn.constName? == some ``Neg.neg &&
            arguments.size == 3 then
          some [arguments[arguments.size - 1]!]
        else none }

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
    { maxPackages := 5, maxNodes := 16, maxDepth := 8 }
    #[sourceSyntax, negationSyntax, sineSyntax, expSyntax]

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
private theorem negationAligned : negationModel.operation = negationOperation := rfl
private theorem sineAligned : sineModel.operation = sineOperation := rfl
private theorem expAligned : expModel.operation = expOperation := rfl

private def sourceMeaning : GoalClosure.Package :=
  { operation := sourceOperation
    model := mkConst ``sourceModel
    aligned := mkConst ``sourceAligned
    prove := fun arguments _ => do
      unless arguments.isEmpty do
        throwError "interval_mixed_instance: source meaning received arguments"
      mkAppM ``Eq.refl #[FrontendEncoder.listExpr (mkConst ``Real) []] }

private def negationMeaning : GoalClosure.Package :=
  { operation := negationOperation
    model := mkConst ``negationModel
    aligned := mkConst ``negationAligned
    prove := fun arguments output => do
      let [input] := arguments
        | throwError "interval_mixed_instance: negation meaning is not unary"
      let expected ← mkAppM ``Neg.neg #[input]
      unless ← isDefEq output expected do
        throwError "interval_mixed_instance: negation recognizer changed the expression"
      mkAppM ``Eq.refl #[output] }

private def sineMeaning : GoalClosure.Package :=
  { operation := sineOperation
    model := mkConst ``sineModel
    aligned := mkConst ``sineAligned
    prove := fun arguments output => do
      let [input] := arguments
        | throwError "interval_mixed_instance: sine meaning is not unary"
      let expected ← mkAppM ``Real.sin #[input]
      unless ← isDefEq output expected do
        throwError "interval_mixed_instance: sine recognizer changed the expression"
      mkAppM ``Eq.refl #[output] }

private def expMeaning : GoalClosure.Package :=
  { operation := expOperation
    model := mkConst ``expModel
    aligned := mkConst ``expAligned
    prove := fun arguments output => do
      let [input] := arguments
        | throwError "interval_mixed_instance: exponential meaning is not unary"
      let expected ← mkAppM ``Real.exp #[input]
      unless ← isDefEq output expected do
        throwError "interval_mixed_instance: exponential recognizer changed the expression"
      mkAppM ``Eq.refl #[output] }

private def meanings : Array GoalClosure.Package :=
  #[sourceMeaning, negationMeaning, sineMeaning, expMeaning]

private meta def reifyGoal (target : Expr) : MetaM (GoalFrontend.Result Bound) := do
  let registry ←
    match goalRegistry? with
    | .ok registry => pure registry
    | .error message =>
        throwError "interval_mixed_instance: invalid registry: {message}"
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

private structure Run where
  result : TargetRun.Result Bound Unit
  reached : TargetRun.Reached Bound

private def runSession? (input : CheckerInput Bound) : Option Run := do
  let .ok session := PolicySession.Session.start factDomain input.baseProgram
      packages input.initialFacts limits
    | none
  let result := TargetRun.drive factDomain input.target.node input.target.fact
    firstOffer limits.policy.maxDecisions session ()
  let .target reached := result.stop | none
  some { result, reached }

private structure Fixture where
  result : TargetRun.Result Bound Unit
  reached : TargetRun.Reached Bound
  registry : ProofRegistry.Registry semantics Name

private def runInput? (input : CheckerInput Bound) : Option Fixture := do
  let some run := runSession? input | none
  let .ok registry := ProofRegistry.build run.result.session.registry proofPackages
    | none
  some { result := run.result, reached := run.reached, registry }

private def fixedInput : CheckerInput Bound :=
  checkerInput

private def liveTrace? : Option (Frontend.Trace Bound) :=
  match runSession? fixedInput with
  | some run => Frontend.trace? run.result.session.state.engine run.result.session.arena
  | none => none

private def exactRuleInput (step : RuleStep Bound) (expected : SeenVersion) : Bool :=
  match step.event.cause with
  | .rule action _ _ => action.inputs == [expected]
  | .transport _ _ => false

private def exactTransportInput (step : TransportStep Bound)
    (expectedEquality : EqualityId) (expectedSource : SeenVersion) : Bool :=
  match step.event.cause with
  | .rule _ _ _ => false
  | .transport equality source =>
      equality == expectedEquality && source == expectedSource

#guard
  liveTrace?.any fun trace =>
    trace.program == extendedProgram &&
      match trace.events with
      | [.instantiation instantiation, .rule sine, .rule negation,
          .transport transport, .rule exp] =>
          instantiation.entry.replayKey == oddnessInstanceSchema.key &&
            instantiation.event.programVersion == 1 &&
            instantiation.event.family == 1 &&
            instantiation.event.substitution == [node 2] &&
            instantiation.event.products == [node 4, node 5] &&
            instantiation.event.newNodes == [node 4, node 5] &&
            instantiation.event.equalities == [{ index := 0 }] &&
            instantiation.event.newEqualities == [{ index := 0 }] &&
            instantiation.event.payload == instantiation.payload &&
            sine.entry.replayKey == sineFactSchema.key &&
            sine.event.node == node 4 &&
            sine.event.version == 1 &&
            sine.event.fact == .unit &&
            exactRuleInput sine { node := node 0, version := 0 } &&
            negation.entry.replayKey == negationFactSchema.key &&
            negation.event.node == node 5 &&
            negation.event.version == 1 &&
            negation.event.fact == .unit &&
            exactRuleInput negation { node := node 4, version := 1 } &&
            transport.entry.replayKey == oddnessEqualitySchema.key &&
            transport.event.node == node 2 &&
            transport.event.version == 1 &&
            transport.event.fact == .unit &&
            exactTransportInput transport { index := 0 }
              { node := node 5, version := 1 } &&
            exp.entry.replayKey == expFactSchema.key &&
            exp.event.node == node 3 &&
            exp.event.version == 1 &&
            exp.event.fact == .atMostThree &&
            exactRuleInput exp { node := node 2, version := 1 }
      | _ => false

private def boundExpr : Bound → Expr
  | .all => mkConst ``MixedFunctions.Bound.all
  | .unit => mkConst ``MixedFunctions.Bound.unit
  | .atMostThree => mkConst ``MixedFunctions.Bound.atMostThree
  | .empty => mkConst ``MixedFunctions.Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``MixedFunctions.Bound)
    (fun fact => pure (boundExpr fact))

private def factBridge : GoalClosure.FactBridge Bound :=
  { runtime := factDomain
    schema := mkConst ``boundSchema
    proveAssumption := fun program valuation factNode fact _ proof => do
      let expected ←
        mkAppM ``SemanticReplay.Semantics.holds
          #[mkConst ``semantics, program, valuation,
            ← boundEncoder.nodeFact { node := factNode, fact }]
      unless ← isDefEq (← inferType proof) expected do
        throwError "interval_mixed_instance: hypothesis does not prove its parsed fact"
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
    finalPrefix := mkConst ``programPrefix
    sameOperations := mkConst ``sameOperations
    top := boundSchema.top }

private meta def emitInput (result : GoalFrontend.Result Bound)
    (base : GoalClosure.BaseProof) : MetaM Expr := do
  let some fixture := runInput? result.input
    | throwError "interval_mixed_instance: search or proof registry failed"
  let some trace := Frontend.trace? fixture.result.session.state.engine
      fixture.result.session.arena
    | throwError "interval_mixed_instance: chronology quotation failed"
  unless trace.program == extendedProgram do
    throwError "interval_mixed_instance: matcher produced an unexpected final graph"
  let context := inputContext result base
  let state ← ProofFrontend.emitTrace context trace.program trace.events
    fixture.registry.emit
  let final ← ProofFrontend.closeTarget context state fixture.reached.seen
    fixture.reached.fact result.input.target
  mkAppM ``closeEvidence #[base.within, state.extension, final]

private meta def proveMixedInstantiation (target : Expr) : MetaM Expr := do
  let result ← reifyGoal target
  unless result.input.baseProgram == baseProgram &&
      result.input.target == fixedInput.target &&
      result.input.initialFacts == fixedInput.initialFacts do
    throwError "interval_mixed_instance: reifier produced an unexpected input"
  let some fallback := GoalClosure.termAt? result.terms (node 0)
    | throwError "interval_mixed_instance: source expression is missing"
  let model ← GoalClosure.proveModel (mkConst ``Real) fallback meanings
    boundEncoder result
  let base ← GoalClosure.proveBase (mkConst ``MixedFunctions.Bound)
    (mkConst ``semantics) boundEncoder result.input
  let facts ← GoalClosure.proveFacts factBridge boundEncoder result base model
  let evidence ← emitInput result base
  let proof ← mkAppM ``Evidence.proof #[evidence, model.valuation, model.proof, facts]
  unless ← isDefEq (← inferType proof) target do
    throwError "interval_mixed_instance: emitted proof has the wrong target"
  pure (← instantiateMVars proof)

syntax (name := intervalMixedInstantiationTac) "interval_mixed_instance" : tactic

@[tactic intervalMixedInstantiationTac] meta def evalIntervalMixedInstantiation :
    Tactic := fun stx => do
  match stx with
  | `(tactic| interval_mixed_instance) =>
      let goal ← getMainGoal
      goal.withContext do
        goal.assign
          (← proveMixedInstantiation (← instantiateMVars (← goal.getType)))
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

/-- Dynamic expression growth and four independent packages close the actual
mixed-function goal through the generic proof frontend. -/
theorem mixedSinNegExp (x : ℝ) : Real.exp (Real.sin (-x)) ≤ 3 := by
  interval_mixed_instance

/-- error: interval_mixed_instance: reifier produced an unexpected input -/
#guard_msgs in
example (x : ℝ) : Real.exp (Real.sin x) ≤ 3 := by
  interval_mixed_instance

/--
info: 'Hex.IntervalMathlib.MixedInstantiationConformance.mixedSinNegExp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mixedSinNegExp

end Hex.IntervalMathlib.MixedInstantiationConformance
