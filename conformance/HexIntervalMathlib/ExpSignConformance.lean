/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.ExpSign
import HexInterval.Experiment.GoalFrontend
import HexInterval.Experiment.GoalClosure
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import HexInterval.Experiment.BranchStart
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
open GoalClosure BranchStart

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
  { parse := fun proposition => do
      let arguments := proposition.getAppArgs
      if proposition.getAppFn.constName? == some ``LE.le &&
          arguments.size ≥ 2 then
        let left := arguments[arguments.size - 2]!
        let right := arguments[arguments.size - 1]!
        let rightType ← inferType right
        if isZero left && rightType == mkConst ``Real then
          pure <| some
            { expression := right
              domain := real
              fact := .nonnegative }
        else
          pure none
      else
        pure none }

private theorem sourceAligned : sourceModel.operation = sourceOperation := rfl

private theorem expAligned : expModel.operation = expOperation := rfl

private def sourceMeaning : GoalClosure.Package :=
  { operation := sourceOperation
    model := mkConst ``sourceModel
    aligned := mkConst ``sourceAligned
    prove := fun arguments _ => do
      unless arguments.isEmpty do
        throwError "interval_exp: source meaning received arguments"
      let empty := FrontendEncoder.listExpr (mkConst ``Real) []
      mkAppM ``Eq.refl #[empty] }

private def expMeaning : GoalClosure.Package :=
  { operation := expOperation
    model := mkConst ``expModel
    aligned := mkConst ``expAligned
    prove := fun arguments output => do
      let [input] := arguments
        | throwError "interval_exp: exponential meaning is not unary"
      let expected ← mkAppM ``Real.exp #[input]
      unless ← isDefEq output expected do
        throwError "interval_exp: recognizer did not preserve exponential meaning"
      mkAppM ``Eq.refl #[output] }

private def meanings : Array GoalClosure.Package :=
  #[sourceMeaning, expMeaning]

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

/-- The live proof fixture covers the target-reachable prefix. Additional
caller facts may append nodes or narrow version-zero facts without changing
the independent exponential proof. -/
private def sameTargetGraph (input : CheckerInput Bound) : Bool :=
  input.baseProgram.operations.toList.take
      checkerInput.baseProgram.operations.size ==
    checkerInput.baseProgram.operations.toList &&
    input.baseProgram.nodes.toList.take checkerInput.baseProgram.nodes.size ==
      checkerInput.baseProgram.nodes.toList &&
    input.target == checkerInput.target

private def spareOperation : Operation :=
  { key := { name := "exp-sign.spare" }, inputs := [], output := real }

#guard
  sameTargetGraph
    { checkerInput with
      baseProgram := { program with operations := operations.push spareOperation } }

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

def invokesExpAt (target : NodeId) (offer : Propagator.Policy.OfferView) : Bool :=
  match offer.key with
  | .invoke invocation =>
      invocation.rule == expRuleKey && invocation.anchor == target
  | _ => false

def invokesExp (offer : Propagator.Policy.OfferView) : Bool :=
  invokesExpAt (node 1) offer

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

def fixtureInput? (input : CheckerInput Bound) : Option Fixture := do
  let .ok session := PolicySession.Session.start factDomain
      input.baseProgram packages input.initialFacts limits
    | none
  let (_, selection, viewed) ← offer? session (invokesExpAt input.target.node)
  let session ←
    match viewed.choose (.select selection) with
    | .rule _ observation next =>
        if observation.outcome == .success then some next else none
    | _ => none
  match ProofRegistry.build session.registry proofPackages with
  | .ok registry => some { session, registry }
  | .error _ => none

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def stopPolicy : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state _ => .stop state }

structure RunFixture extends Fixture where
  reached : TargetRun.Reached Bound
  events : Array (TargetRun.Event Bound)

def runWith? (runtimePackages : Array (Package Bound))
    (input : CheckerInput Bound) (controller : TargetRun.Controller Bound Unit)
    (fuel : Nat) (scope : Propagator.Policy.ScopeId := { index := 0 }) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain
      input.baseProgram runtimePackages input.initialFacts limits scope
    | none
  some (TargetRun.drive factDomain input.target.node input.target.fact controller
    fuel session ())

def runRaw? (input : CheckerInput Bound) (controller : TargetRun.Controller Bound Unit)
    (fuel : Nat) (scope : Propagator.Policy.ScopeId := { index := 0 }) :
    Option (TargetRun.Result Bound Unit) :=
  runWith? packages input controller fuel scope

def runInput? (input : CheckerInput Bound)
    (scope : Propagator.Policy.ScopeId := { index := 0 }) : Option RunFixture := do
  let result <- runRaw? input firstOffer limits.policy.maxDecisions scope
  let .target reached := result.stop | none
  match ProofRegistry.build result.session.registry proofPackages with
  | .ok registry =>
      some { session := result.session, registry, reached, events := result.events }
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

/-! ## Live zero-split child sessions -/

private def splitOffer? (view : Propagator.Policy.View Bound) :
    Option Propagator.Policy.OfferView :=
  view.offers.toList.find? fun offer =>
    match offer.key with
    | .invoke invocation => invocation.rule == splitRuleKey
    | .split _ _ _ _ => true
    | _ => false

private def splitPolicy : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match splitOffer? view with
      | some offer => .select offer state
      | none => .stop state }

private def signSplitter : BranchStart.Splitter Bound :=
  { split := fun graph target instruction parent point =>
      if graph.node? target == some instruction && instruction.domain == real &&
          parent == .all && point == 0 then
        some (.nonnegative, .negative)
      else
        none }

private def branchLimits : BranchStart.Limits :=
  { maxDepth := 4, maxScopes := 8 }

private def preparedResult? : Option
    (ULift.{1, 0} (BranchStart.State × BranchStart.Children Bound)) :=
  match runWith? splitPackages checkerInput splitPolicy limits.policy.maxDecisions with
  | none => none
  | some result =>
      match result.stop with
      | .split plan =>
          match BranchStart.prepare branchLimits
              (BranchStart.State.start result.session) result.session plan
              checkerInput.target signSplitter with
          | .ok prepared => some (ULift.up prepared)
          | .error _ => none
      | _ => none

private def prepared? : Option (ULift.{1, 0} (BranchStart.Children Bound)) :=
  preparedResult?.map fun lifted => ULift.up lifted.down.2

private def splitRun? : Option (TargetRun.Result Bound Unit) :=
  runWith? splitPackages checkerInput splitPolicy limits.policy.maxDecisions

private def planError? (change : Propagator.Policy.SplitPlan Bound →
    Propagator.Policy.SplitPlan Bound)
    (branchBudget : BranchStart.Limits := branchLimits) : Option BranchStart.Error :=
  match splitRun? with
  | some result =>
      match result.stop with
      | .split plan =>
          match BranchStart.prepare branchBudget
              (BranchStart.State.start result.session) result.session (change plan)
              checkerInput.target signSplitter with
          | .error error => some error
          | .ok _ => none
      | _ => none
  | none => none

private def unrelatedAction? (result : TargetRun.Result Bound Unit)
    (plan : Propagator.Policy.SplitPlan Bound) : Option Action := do
  let engine := result.session.state.engine
  let index ← (List.range engine.applications.size).find?
    (fun index => index != plan.origin.application.index)
  let applicationId : ApplicationId := { index }
  let application ← engine.applications[index]?
  let rule ← engine.rules[application.rule.index]?
  let inputs ← engine.seenVersions? application.watches
  let views ← engine.factViews? application.watches
  match engine.issueApplication applicationId application rule inputs views with
  | .request request _ =>
      if engine.actionFresh request.action then some request.action else none
  | _ => none

#guard
  splitRun?.any fun result =>
    match ProofRegistry.build result.session.registry splitProofPackages with
    | .ok _ => true
    | .error _ => false

#guard
  splitRun?.any fun result =>
    match ProofRegistry.build result.session.registry proofPackages with
    | .error (.semantic (.packageCount 3 2)) => true
    | _ => false

private def branchFact (side : Bound) : NodeFact Bound :=
  { node := node 0, fact := side }

private def branchFacts (side : Bound) : List (NodeFact Bound) :=
  branchFact side :: baseFacts

private def branchInitial (side : Bound) : Array Bound := #[side, .all]

private def branchInput (side : Bound) : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := branchInitial side
    target := checkerInput.target }

private def inheritBranch (side : Bound) (observed : NodeId)
    (different : observed ≠ node 0) (fact : Bound)
    (found : (branchInput side).initialFacts[observed.index]? = some fact) :
    Evidence
      (semantics.Entails program baseFacts { node := observed, fact }) :=
  { proof := by
      intro _ _ assumptions
      cases observed with
      | mk index =>
          cases index with
          | zero => simp [node] at different
          | succ index =>
              cases index with
              | zero =>
                  simp [branchInput, branchInitial] at found
                  subst fact
                  exact assumptions _ (by simp [baseFacts, node])
              | succ index => simp [branchInput, branchInitial] at found }

private def leftInput : CheckerInput Bound := branchInput .nonnegative
private def rightInput : CheckerInput Bound := branchInput .negative
private def leftScope : Propagator.Policy.ScopeId := { index := 1 }
private def rightScope : Propagator.Policy.ScopeId := { index := 2 }
private def leftFacts : List (NodeFact Bound) := branchFacts .nonnegative
private def rightFacts : List (NodeFact Bound) := branchFacts .negative

private def leftSeed :
    ProofEmitter.BranchSeed semantics leftInput baseFacts
      (branchFact .nonnegative) :=
  ProofEmitter.BranchSeed.make leftInput (branchFact .nonnegative)
    (by rfl) (by rfl) (inheritBranch .nonnegative)

private def rightSeed :
    ProofEmitter.BranchSeed semantics rightInput baseFacts
      (branchFact .negative) :=
  ProofEmitter.BranchSeed.make rightInput (branchFact .negative)
    (by rfl) (by rfl) (inheritBranch .negative)

#guard
  prepared?.any fun lifted =>
    let children := lifted.down
    children.depth == 1 &&
      children.parent.baseProgram == checkerInput.baseProgram &&
      children.parent.initialFacts == checkerInput.initialFacts &&
      children.parent.target == checkerInput.target &&
      children.leftScope == leftScope &&
      children.left.baseProgram == leftInput.baseProgram &&
      children.left.initialFacts == leftInput.initialFacts &&
      children.left.target == leftInput.target &&
      children.rightScope == rightScope &&
      children.right.baseProgram == rightInput.baseProgram &&
      children.right.initialFacts == rightInput.initialFacts &&
      children.right.target == rightInput.target &&
      children.plan.point == 0 && children.plan.fact == .all

#guard
  preparedResult?.any fun lifted =>
    let state := lifted.down.1
    state.createdScopes == 3 && state.nextScope == 3

#guard
  runInput? leftInput leftScope |>.any fun fixture =>
    fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .nonnegative && fixture.events.size == 1 &&
      fixture.session.state.engine.facts == #[.nonnegative, .nonnegative]

#guard
  runInput? rightInput rightScope |>.any fun fixture =>
    fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .nonnegative && fixture.events.size == 1 &&
      fixture.session.state.engine.facts == #[.negative, .nonnegative]

private def closedChildren? : Option
    (ULift.{1, 0} (TargetRun.Reached Bound × TargetRun.Reached Bound)) :=
  match prepared? with
  | none => none
  | some lifted =>
      let children := lifted.down
      match runRaw? children.left firstOffer limits.policy.maxDecisions
          children.leftScope,
        runRaw? children.right firstOffer limits.policy.maxDecisions
          children.rightScope with
      | some left, some right =>
          (BranchStart.closedTargets? factDomain children left right).map ULift.up
      | _, _ => none

#guard closedChildren?.isSome

#guard
  prepared?.any fun lifted =>
    let children := lifted.down
    match runRaw? children.left stopPolicy limits.policy.maxDecisions
        children.leftScope,
      runRaw? children.right firstOffer limits.policy.maxDecisions
        children.rightScope with
    | some left, some right =>
        (BranchStart.closedTargets? factDomain children left right).isNone
    | _, _ => false

#guard
  prepared?.any fun lifted =>
    let children := lifted.down
    match runRaw? children.left firstOffer limits.policy.maxDecisions { index := 99 },
      runRaw? children.right firstOffer limits.policy.maxDecisions children.rightScope with
    | some left, some right =>
        (BranchStart.closedTargets? factDomain children left right).isNone
    | _, _ => false

#guard planError? (fun plan => plan)
  ({ branchLimits with maxDepth := 0 }) == some .depthLimit

#guard planError? (fun plan => plan)
  ({ branchLimits with maxScopes := 2 }) == some .scopeLimit

#guard
  planError? (fun plan =>
    { plan with scope := { index := plan.scope.index + 1 } }) == some .wrongScope

#guard
  match splitRun?, preparedResult? with
  | some result, some lifted =>
      match result.stop with
      | .split plan =>
          match BranchStart.prepare branchLimits lifted.down.1 result.session plan
              checkerInput.target signSplitter with
          | .error .wrongState => true
          | _ => false
      | _ => false
  | _, _ => false

#guard
  match splitRun?,
      runWith? splitPackages checkerInput splitPolicy limits.policy.maxDecisions
        { index := 7 } with
  | some result, some unrelated =>
      match result.stop with
      | .split plan =>
          match BranchStart.prepare branchLimits
              (BranchStart.State.start unrelated.session) result.session plan
              checkerInput.target signSplitter with
          | .error .wrongState => true
          | _ => false
      | _ => false
  | _, _ => false

#guard
  planError? (fun plan =>
    { plan with suggestion := { index := plan.suggestion.index + 1 } }) ==
      some .unknownSuggestion

-- `actionFresh` deliberately ignores the request serial; exact retained-origin
-- authentication must still reject a serial-spliced plan.
#guard
  planError? (fun plan =>
    let origin := { plan.origin with serial := plan.origin.serial + 1 }
    { plan with
      origin
      source := Propagator.Policy.invocationOfAction plan.scope origin }) ==
        some .wrongOrigin

#guard
  planError? (fun plan => { plan with point := 1 }) == some .wrongSuggestion

#guard
  planError? (fun plan => { plan with node := node 1 }) == some .wrongSuggestion

#guard
  planError? (fun plan => { plan with reason := .midpoint }) == some .wrongSuggestion

#guard
  planError? (fun plan => { plan with version := plan.version + 1 }) ==
    some .wrongSuggestionVersion

-- The branch boundary repeats the endpoint preflight instead of relying on a
-- caller to have obtained the plan from a bounded policy view.
#guard
  planError? (fun plan =>
    { plan with point := Dyadic.ofIntWithPrec 1 16 }) == some .endpointLimit

#guard
  match splitRun? with
  | some result =>
      match result.stop with
      | .split plan =>
          match unrelatedAction? result plan with
          | some origin =>
              let forged :=
                { plan with
                  origin
                  source := Propagator.Policy.invocationOfAction plan.scope origin }
              match BranchStart.prepare branchLimits
                  (BranchStart.State.start result.session) result.session forged
                  checkerInput.target signSplitter with
              | .error .wrongOrigin => true
              | _ => false
          | none => false
      | _ => false
  | none => false

#guard
  match runWith? splitPackages checkerInput splitPolicy limits.policy.maxDecisions with
  | some result =>
      match result.stop with
      | .split plan =>
          let duplicate : BranchStart.Splitter Bound :=
            { split := fun _ _ _ _ _ => some (.nonnegative, .nonnegative) }
          match BranchStart.prepare branchLimits
              (BranchStart.State.start result.session) result.session plan
              checkerInput.target duplicate with
          | .error .duplicateChild => true
          | _ => false
      | _ => false
  | none => false

/-! ## Operation-composed semantics at an arbitrary graph node -/

private def nestedInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 1] }

private def nestedProgram : Program :=
  { operations, nodes := #[sourceInstruction, expInstruction, nestedInstruction] }

private def nestedInput : CheckerInput Bound :=
  { baseProgram := nestedProgram
    initialFacts := #[.all, .all, .all]
    target := { node := node 2, fact := .nonnegative } }

private def nonnegativeEvidence :
    Evidence
      (semantics.Entails program baseFacts
        { node := node 1, fact := .nonnegative }) :=
  { proof :=
      expEntails program baseFacts (node 1) expInstruction (node 0)
        (by rfl) (by rfl) (by rfl) }

private def weakerTarget? :
    Option
      (Evidence
        (semantics.Entails program baseFacts
          { node := node 1, fact := .all })) :=
  ProofEmitter.closeFact boundSchema program baseFacts (node 1)
    .nonnegative .all nonnegativeEvidence

/-- A strictly stronger installed fact closes a weaker requested target
through the fact-domain intersection theorem, not the runtime target test. -/
theorem closesWeaker :
    semantics.Entails program baseFacts { node := node 1, fact := .all } :=
  (replayGet weakerTarget? (by rfl)).proof

private def topEvidence :
    Evidence
      (semantics.Entails program baseFacts
        { node := node 1, fact := .all }) := by
  simpa [boundSchema, expInstruction] using
    (ProofEmitter.topFact boundSchema program baseFacts (node 1)
      expInstruction (by rfl))

#guard
  (ProofEmitter.closeFact boundSchema program baseFacts (node 1)
    .all .nonnegative topEvidence).isNone

#guard
  runInput? nestedInput |>.any fun fixture =>
    fixture.reached.seen == ({ node := node 2, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .nonnegative && fixture.events.size == 2 &&
      fixture.session.state.engine.facts ==
        #[.all, .nonnegative, .nonnegative] &&
      fixture.session.state.engine.chronology == #[.fact 0, .fact 1]

#guard
  runRaw? nestedInput firstOffer 0 |>.any fun result =>
    match result.stop with
    | .fuel => result.events.isEmpty
    | _ => false

#guard
  runRaw? nestedInput stopPolicy limits.policy.maxDecisions |>.any fun result =>
    match result.stop with
    | .policyStop live => live == 2 && result.events.isEmpty
    | _ => false

private def initiallyReached : CheckerInput Bound :=
  { nestedInput with target := { node := node 0, fact := .all } }

#guard
  runRaw? initiallyReached firstOffer 0 |>.any fun result =>
    match result.stop with
    | .target reached =>
        reached.seen == ({ node := node 0, version := 0 } : SeenVersion) &&
          reached.fact == .all && result.events.isEmpty
    | _ => false

private def unreachableTarget : CheckerInput Bound :=
  { nestedInput with target := { node := node 2, fact := .empty } }

#guard
  runRaw? unreachableTarget firstOffer limits.policy.maxDecisions |>.any fun result =>
    match result.stop with
    | .saturated => result.events.size == 2 && result.session.complete
    | _ => false

private def nestedAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := expRuleKey
    node := node 2
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node 2] }

private def nestedContext : RuleFactContext nestedInput nestedAction :=
  { program := nestedProgram
    basePrefix := ProgramPrefix.refl nestedProgram
    assumptions := []
    proposed := { node := node 2, fact := .nonnegative } }

#guard (expFactSchema.replay nestedInput nestedAction nestedContext ()).isSome

private def sourceContext : RuleFactContext nestedInput nestedAction :=
  { nestedContext with
    proposed := { node := node 0, fact := .nonnegative } }

#guard (expFactSchema.replay nestedInput nestedAction sourceContext ()).isNone

private def nestedEvidence : Evidence
    (semantics.Entails nestedProgram [] nestedInput.target) :=
  (expFactSchema.replay nestedInput nestedAction nestedContext ()).get (by rfl)

private noncomputable def nestedValuation (x : ℝ) : NodeId → ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => Real.exp x
  | ⟨2⟩ => Real.exp (Real.exp x)
  | _ => 0

private theorem nestedModels (x : ℝ) :
    semantics.models nestedProgram (nestedValuation x) := by
  refine ⟨?_, ?_⟩
  · simp [nestedProgram, operations, operationModels, sourceModel, expModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, nestedProgram, sourceInstruction] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, nestedProgram, expInstruction] at found
          subst instruction
          exact ⟨expModel, by rfl, by rfl⟩
      | succ index =>
          cases index with
          | zero =>
              simp [Program.node?, nestedProgram, nestedInstruction] at found
              subst instruction
              exact ⟨expModel, by rfl, by rfl⟩
          | succ index =>
              simp [Program.node?, nestedProgram] at found

theorem nestedExp (x : ℝ) : 0 ≤ Real.exp (Real.exp x) := by
  have holds := nestedEvidence.proof (nestedValuation x) (nestedModels x)
    (by simp)
  exact holds

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .nonnegative => mkConst ``Bound.nonnegative
  | .negative => mkConst ``Bound.negative
  | .empty => mkConst ``Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))

private def factBridge : GoalClosure.FactBridge Bound :=
  { runtime := factDomain
    schema := mkConst ``boundSchema
    proveAssumption := fun program valuation node fact _ proof => do
      let nodeFact ← boundEncoder.nodeFact { node, fact }
      let expected ←
        mkAppM ``SemanticReplay.Semantics.holds
          #[mkConst ``semantics, program, valuation, nodeFact]
      unless ← isDefEq (← inferType proof) expected do
        throwError "interval_exp: hypothesis does not prove its parsed fact"
      pure proof }

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
    | throwError "interval_exp: compiled search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "interval_exp: chronology quotation failed"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  let target := { node := node 1, version := 1 : SeenVersion }
  let some proof := ProofFrontend.findProof? state.known target .nonnegative
    | throwError "interval_exp: target fact was not emitted"
  pure proof

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

private theorem branchWithin (side : Bound) :
    FactsWithin program (branchFacts side) := by
  intro fact member
  simp only [branchFacts, branchFact, baseFacts, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [program, node]

private def splitContext (input facts within : Expr)
    (factValues : List (NodeFact Bound)) : ProofFrontend.Context Bound Name :=
  { encoder := boundEncoder
    resolveSchema := pure
    semantics := mkConst ``semantics
    domain := mkConst ``boundSchema
    laws := mkConst ``laws
    stableLaw := mkConst ``stableLaw
    input
    assumed := ``seedAssumed
    baseFacts := factValues
    baseFactsTerm := facts
    baseProgram := program
    baseProgramTerm := mkConst ``program
    basePrefix := mkConst ``basePrefix
    baseWithin := within
    initialExtension := mkConst ``initialExtension
    finalPrefix := mkConst ``basePrefix
    sameOperations := mkConst ``sameOperations
    top := boundSchema.top }

private def leftContext : ProofFrontend.Context Bound Name :=
  splitContext (mkConst ``leftInput) (mkConst ``leftFacts)
    (mkApp (mkConst ``branchWithin) (mkConst ``Bound.nonnegative)) leftFacts

private def rightContext : ProofFrontend.Context Bound Name :=
  splitContext (mkConst ``rightInput) (mkConst ``rightFacts)
    (mkApp (mkConst ``branchWithin) (mkConst ``Bound.negative)) rightFacts

private def splitParent : Evidence
    (semantics.Entails program baseFacts (branchFact .all)) :=
  ProofEmitter.assumed (by simp [baseFacts, branchFact, node])

private meta def emitChild (context : ProofFrontend.Context Bound Name)
    (input : CheckerInput Bound) (scope : Propagator.Policy.ScopeId)
    (seed : Expr) (side : Bound) : MetaM Expr := do
  let some fixture := runInput? input scope
    | throwError "interval_exp_split: child search failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "interval_exp_split: child chronology quotation failed"
  unless trace.program == input.baseProgram do
    throwError "interval_exp_split: child trace changed the expression graph"
  let [.rule step] := trace.events
    | throwError "interval_exp_split: child trace is not exactly one fact rule"
  unless fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .nonnegative && fixture.events.size == 1 &&
      fixture.session.state.engine.facts == #[side, .nonnegative] &&
      step.entry.replayKey == expFactSchema.key &&
      step.event.programVersion == 0 && step.event.node == node 1 &&
      step.event.previous == ({ node := node 1, version := 0 } : SeenVersion) &&
      step.event.fact == .nonnegative && step.event.version == 1 &&
      step.assumptions == [branchFact side] && step.previous == .all do
    throwError "interval_exp_split: child result or quoted rule trace drifted"
  let state ← ProofFrontend.emitBranch context input seed trace.program
    trace.events fixture.registry.emit
  ProofFrontend.closeTarget context state fixture.reached.seen
    fixture.reached.fact input.target

private meta def emitSplit : MetaM Expr := do
  let left ← emitChild leftContext leftInput leftScope
    (mkConst ``leftSeed) .nonnegative
  let right ← emitChild rightContext rightInput rightScope
    (mkConst ``rightSeed) .negative
  let result ←
    mkAppM ``ProofEmitter.replaySplit
      #[mkConst ``signSplit, mkConst ``program, mkConst ``baseFacts,
        ← boundEncoder.nodeId (node 0), ← boundEncoder.fact .all,
        mkConst ``Unit.unit, ← boundEncoder.fact .nonnegative,
        ← boundEncoder.fact .negative,
        ← boundEncoder.nodeFact checkerInput.target,
        mkConst ``splitParent, left, right]
  ProofFrontend.replayResult result

private meta def emitInput (result : GoalFrontend.Result Bound)
    (base : GoalClosure.BaseProof) : MetaM Expr := do
  let some fixture := runInput? result.input
    | throwError "interval_exp: dynamic search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "interval_exp: dynamic chronology quotation failed"
  unless trace.program == result.input.baseProgram do
    throwError "interval_exp: exponential rule unexpectedly changed the graph"
  let state ← ProofFrontend.emitTrace (inputContext result base)
    trace.program trace.events fixture.registry.emit
  ProofFrontend.closeTarget (inputContext result base) state fixture.reached.seen
    fixture.reached.fact result.input.target

private def expTarget (x : ℝ) : Prop :=
  0 ≤ Real.exp x

private meta def proveModeledExp (target : Expr) : MetaM Expr := do
  let result ← reifyGoal target
  let some fallback := GoalClosure.termAt? result.terms { index := 0 }
    | throwError "interval_exp model test: missing source expression"
  if (← observing? <| GoalClosure.proveModel (mkConst ``Real) fallback
      #[sourceMeaning] boundEncoder result).isSome then
    throwError "interval_exp model test: missing meaning package was accepted"
  let falseExp : GoalClosure.Package :=
    { expMeaning with prove := fun _ _ => pure (mkConst ``True.intro) }
  if (← observing? <| GoalClosure.proveModel (mkConst ``Real) fallback
      #[sourceMeaning, falseExp] boundEncoder result).isSome then
    throwError "interval_exp model test: false node link was accepted"
  let model ← GoalClosure.proveModel (mkConst ``Real) fallback meanings
    boundEncoder result
  let base ← GoalClosure.proveBase (mkConst ``Bound) (mkConst ``semantics)
    boundEncoder result.input
  let facts ← GoalClosure.proveFacts factBridge boundEncoder result base model
  let matching := result.baseFacts.zipIdx.find? fun item =>
    item.1 == result.input.target
  let evidence ←
    match matching with
    | some (fact, index) => do
        let factTerm ← boundEncoder.nodeFact fact
        let someFact ← mkAppM ``Option.some #[factTerm]
        let found ← mkAppM ``Eq.refl #[someFact]
        mkAppM ``seedAssumed
          #[base.program, base.facts, mkNatLit index, factTerm, found]
    | none =>
        emitInput result base
  let proof ←
    mkAppM ``Evidence.proof #[evidence, model.valuation, model.proof, facts]
  unless ← isDefEq (← inferType proof) target do
    throwError "interval_exp model test: modeled replay has the wrong target"
  pure (← instantiateMVars proof)

syntax (name := intervalExpModelTac) "interval_exp_model" : tactic

@[tactic intervalExpModelTac] meta def evalIntervalExpModel : Tactic := fun stx => do
  match stx with
  | `(tactic| interval_exp_model) =>
      let goal ← getMainGoal
      goal.withContext do
        goal.assign (← proveModeledExp (← instantiateMVars (← goal.getType)))
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

theorem tacticExpModeled (x : ℝ) : 0 ≤ Real.exp x := by
  interval_exp_model

/--
info: 'Hex.IntervalMathlib.ExpSignConformance.tacticExpModeled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tacticExpModeled

theorem tacticExpModeledSeed (x : ℝ) (_h : 0 ≤ Real.exp x) :
    0 ≤ Real.exp x := by
  interval_exp_model

/--
info: 'Hex.IntervalMathlib.ExpSignConformance.tacticExpModeledSeed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tacticExpModeledSeed

theorem tacticExpModeledExtra (x y : ℝ) (_hy : 0 ≤ Real.exp y) :
    0 ≤ Real.exp x := by
  interval_exp_model

theorem tacticExpModeledNested (x : ℝ) :
    0 ≤ Real.exp (Real.exp x) := by
  interval_exp_model

private meta def proveExp (target : Expr) : MetaM Expr := do
  let reified ← reifyGoal target
  unless sameTargetGraph reified.input do
    throwError "interval_exp: goal reification produced an unexpected target graph"
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

private meta def proveSplit (target : Expr) : MetaM Expr := do
  let context ← getLCtx
  for declaration in context do
    unless declaration.isImplementationDetail do
      let saved ← saveState
      let candidate? ← observing? <|
        mkAppM ``expTarget #[mkFVar declaration.fvarId]
      match candidate? with
      | some candidate =>
          if ← isDefEq candidate target then
            let evidence ← emitSplit
            let proof ←
              mkAppM ``closeExp #[mkFVar declaration.fvarId, evidence]
            unless ← isDefEq (← inferType proof) target do
              throwError "interval_exp_split: joined proof has the wrong target"
            return (← instantiateMVars proof)
          saved.restore
      | none => saved.restore
  throwError "interval_exp_split: expected a goal `0 ≤ Real.exp x`"

syntax (name := intervalExpSplitTac) "interval_exp_split" : tactic

@[tactic intervalExpSplitTac] meta def evalIntervalExpSplit : Tactic := fun stx => do
  match stx with
  | `(tactic| interval_exp_split) =>
      let goal ← getMainGoal
      goal.withContext do
        let proof ← proveSplit (← instantiateMVars (← goal.getType))
        goal.assign proof
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

/-- Both live children run the arbitrary exponential propagator, replay their
one-event traces, and close only after the zero split coverage theorem joins
their target proofs. -/
theorem tacticExpSplit (x : ℝ) : 0 ≤ Real.exp x := by
  interval_exp_split

/--
info: 'Hex.IntervalMathlib.ExpSignConformance.tacticExpSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tacticExpSplit

set_option linter.unusedTactic false in
example : True := by
  run_tac
    if (← observing? <| emitChild leftContext rightInput
        rightScope (mkConst ``rightSeed) .negative).isSome then
      throwError "interval_exp_split: mismatched child input was accepted"
    if (← observing? <| emitChild rightContext rightInput
        rightScope (mkConst ``leftSeed) .negative).isSome then
      throwError "interval_exp_split: mismatched branch seed was accepted"
  trivial

theorem tacticExpExtra (x y : ℝ) (_hy : 0 ≤ Real.exp y) :
    0 ≤ Real.exp x := by
  interval_exp

theorem tacticExpDuplicate (x : ℝ) (_h₁ _h₂ : 0 ≤ Real.exp x) :
    0 ≤ Real.exp x := by
  interval_exp

theorem tacticExpNat (x : ℝ) (n : Nat) (_hn : 0 ≤ n) :
    0 ≤ Real.exp x := by
  interval_exp

theorem tacticExpUnsupported (x y z : ℝ) (_h : 0 ≤ y * z) :
    0 ≤ Real.exp x := by
  interval_exp

example (_x : ℝ) : True := by
  fail_if_success interval_exp
  trivial

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example (x : ℝ) (h₁ h₂ : 0 ≤ Real.exp x) : True := by
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
        result.terms.size == 2 && seed.assumptions.length == 2 &&
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

/-! ## One proved child joined with one proof-refuted child -/

private def outputSplitKey : RuleKey :=
  { name := "exp-sign.output.split-zero" }

private def outputSplitRule : Registration :=
  { key := outputSplitKey
    head := expKey
    kind := .split
    watches := [.result]
    writes := [] }

private def outputSplitPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    requiredOperations := #[expOperation]
    handlers :=
      #[Handler.statelessDroppingDrafts outputSplitRule splitInvoke] }

private def outputSplitPackages : Array (Package Bound) :=
  #[sourcePackage, expPackage, outputSplitPackage]

private def outputSplitOffer? (view : Propagator.Policy.View Bound) :
    Option Propagator.Policy.OfferView :=
  view.offers.toList.find? fun offer =>
    match offer.key with
    | .invoke invocation => invocation.rule == outputSplitKey
    | .split _ target _ _ => target.node == node 1
    | _ => false

private def outputSplitPolicy : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match outputSplitOffer? view with
      | some offer => .select offer state
      | none => .stop state }

private def outputPrepared? : Option (ULift.{1, 0} (BranchStart.Children Bound)) :=
  match runWith? outputSplitPackages checkerInput outputSplitPolicy
      limits.policy.maxDecisions with
  | some result =>
      match result.stop with
      | .split plan =>
          match BranchStart.prepare branchLimits
              (BranchStart.State.start result.session) result.session plan
              checkerInput.target signSplitter with
          | .ok (_, children) => some (ULift.up children)
          | .error _ => none
      | _ => none
  | none => none

private def outputFact (side : Bound) : NodeFact Bound :=
  { node := node 1, fact := side }

private def outputFacts (side : Bound) : List (NodeFact Bound) :=
  outputFact side :: baseFacts

private def outputInitial (side : Bound) : Array Bound := #[.all, side]

private def outputInput (side : Bound) : CheckerInput Bound :=
  { baseProgram := program
    initialFacts := outputInitial side
    target := checkerInput.target }

private def outputLeftInput : CheckerInput Bound := outputInput .nonnegative
private def outputRightInput : CheckerInput Bound := outputInput .negative
private def outputLeftFacts : List (NodeFact Bound) := outputFacts .nonnegative
private def outputRightFacts : List (NodeFact Bound) := outputFacts .negative
private def outputLeftScope : Propagator.Policy.ScopeId := { index := 1 }
private def outputRightScope : Propagator.Policy.ScopeId := { index := 2 }

private def inheritOutput (side : Bound) (observed : NodeId)
    (different : observed ≠ node 1) (fact : Bound)
    (found : (outputInput side).initialFacts[observed.index]? = some fact) :
    Evidence
      (semantics.Entails program baseFacts { node := observed, fact }) :=
  { proof := by
      intro _ _ assumptions
      cases observed with
      | mk index =>
          cases index with
          | zero =>
              simp [outputInput, outputInitial] at found
              subst fact
              exact assumptions _ (by simp [baseFacts, node])
          | succ index =>
              cases index with
              | zero => simp [node] at different
              | succ index => simp [outputInput, outputInitial] at found }

private def outputLeftSeed :
    ProofEmitter.BranchSeed semantics outputLeftInput baseFacts
      (outputFact .nonnegative) :=
  ProofEmitter.BranchSeed.make outputLeftInput (outputFact .nonnegative)
    (by rfl) (by rfl) (inheritOutput .nonnegative)

private def outputRightSeed :
    ProofEmitter.BranchSeed semantics outputRightInput baseFacts
      (outputFact .negative) :=
  ProofEmitter.BranchSeed.make outputRightInput (outputFact .negative)
    (by rfl) (by rfl) (inheritOutput .negative)

private theorem outputWithin (side : Bound) :
    FactsWithin program (outputFacts side) := by
  intro fact member
  simp only [outputFacts, outputFact, baseFacts, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [program, node]

private def outputLeftContext : ProofFrontend.Context Bound Name :=
  splitContext (mkConst ``outputLeftInput) (mkConst ``outputLeftFacts)
    (mkApp (mkConst ``outputWithin) (mkConst ``Bound.nonnegative))
    outputLeftFacts

private def outputRightContext : ProofFrontend.Context Bound Name :=
  splitContext (mkConst ``outputRightInput) (mkConst ``outputRightFacts)
    (mkApp (mkConst ``outputWithin) (mkConst ``Bound.negative))
    outputRightFacts

private def outputParent : Evidence
    (semantics.Entails program baseFacts (outputFact .all)) :=
  ProofEmitter.assumed (by simp [baseFacts, outputFact, node])

private def sameChecker (left right : CheckerInput Bound) : Bool :=
  left.baseProgram == right.baseProgram &&
    left.initialFacts == right.initialFacts && left.target == right.target

#guard
  outputPrepared?.any fun lifted =>
    let children := lifted.down
    children.depth == 1 && sameChecker children.parent checkerInput &&
      sameChecker children.left outputLeftInput &&
      sameChecker children.right outputRightInput &&
      children.leftScope == outputLeftScope &&
      children.rightScope == outputRightScope

#guard
  runRaw? outputLeftInput firstOffer limits.policy.maxDecisions
      outputLeftScope |>.any fun result =>
    match result.stop with
    | .target reached =>
        reached.seen == ({ node := node 1, version := 0 } : SeenVersion) &&
          reached.fact == .nonnegative && result.events.isEmpty
    | _ => false

#guard
  runRaw? outputRightInput firstOffer limits.policy.maxDecisions
      outputRightScope |>.any fun result =>
    match result.stop with
    | .contradiction =>
        result.session.state.engine.facts == #[.all, .empty] &&
          result.session.state.engine.versions == #[0, 1] &&
          result.events.size == 1
    | _ => false

#guard
  fixture?.any fun fixture =>
    fixture.registry.refute.find? .empty == some ``emptyRefute &&
      fixture.registry.refute.find? .all == none

private meta def emitOutputTarget (input : CheckerInput Bound)
    (scope : Propagator.Policy.ScopeId) : MetaM Expr := do
  let some result := runRaw? input firstOffer limits.policy.maxDecisions scope
    | throwError "interval_exp_refute: target child did not start"
  let .target reached := result.stop
    | throwError "interval_exp_refute: target child did not close"
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | throwError "interval_exp_refute: target child registry failed"
  let some trace := Frontend.trace? result.session.state.engine result.session.arena
    | throwError "interval_exp_refute: target child quotation failed"
  let state ← ProofFrontend.emitBranch outputLeftContext input
    (mkConst ``outputLeftSeed) trace.program trace.events registry.emit
  ProofFrontend.closeTarget outputLeftContext state reached.seen reached.fact
    input.target

private meta def emitOutputRefute (input : CheckerInput Bound)
    (scope : Propagator.Policy.ScopeId) : MetaM Expr := do
  let some result := runRaw? input firstOffer limits.policy.maxDecisions scope
    | throwError "interval_exp_refute: contradiction child did not start"
  let .contradiction := result.stop
    | throwError "interval_exp_refute: contradiction child did not contradict"
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | throwError "interval_exp_refute: contradiction child registry failed"
  let some trace := Frontend.trace? result.session.state.engine result.session.arena
    | throwError "interval_exp_refute: contradiction child quotation failed"
  unless trace.program == input.baseProgram do
    throwError "interval_exp_refute: contradiction trace changed the graph"
  let [.rule step] := trace.events
    | throwError "interval_exp_refute: contradiction trace is not exactly one rule"
  unless step.entry.replayKey == expFactSchema.key &&
      step.event.programVersion == 0 && step.event.node == node 1 &&
      step.event.previous == ({ node := node 1, version := 0 } : SeenVersion) &&
      step.event.fact == .empty && step.event.version == 1 &&
      step.previous == .negative do
    throwError "interval_exp_refute: contradiction rule trace drifted"
  let state ← ProofFrontend.emitBranch outputRightContext input
    (mkConst ``outputRightSeed) trace.program trace.events registry.emit
  ProofFrontend.refuteCurrent outputRightContext state registry.refute
    result.session.state.engine.facts result.session.state.engine.versions
    input.target

private meta def emitOutputSplitRefute : MetaM Expr := do
  let some lifted := outputPrepared?
    | throwError "interval_exp_refute: output split was not prepared"
  let children := lifted.down
  unless sameChecker children.left outputLeftInput &&
      sameChecker children.right outputRightInput do
    throwError "interval_exp_refute: prepared children differ from proof contexts"
  let left ← emitOutputTarget children.left children.leftScope
  let right ← emitOutputRefute children.right children.rightScope
  let result ←
    mkAppM ``ProofEmitter.replaySplit
      #[mkConst ``signSplit, mkConst ``program, mkConst ``baseFacts,
        ← boundEncoder.nodeId (node 1), ← boundEncoder.fact .all,
        mkConst ``Unit.unit, ← boundEncoder.fact .nonnegative,
        ← boundEncoder.fact .negative,
        ← boundEncoder.nodeFact checkerInput.target,
        mkConst ``outputParent, left, right]
  ProofFrontend.replayResult result

private meta def proveSplitRefute (target : Expr) : MetaM Expr := do
  let context ← getLCtx
  for declaration in context do
    unless declaration.isImplementationDetail do
      let saved ← saveState
      let candidate? ← observing? <| mkAppM ``expTarget #[mkFVar declaration.fvarId]
      match candidate? with
      | some candidate =>
          if ← isDefEq candidate target then
            let evidence ← emitOutputSplitRefute
            let proof ← mkAppM ``closeExp #[mkFVar declaration.fvarId, evidence]
            unless ← isDefEq (← inferType proof) target do
              throwError "interval_exp_refute: joined proof has the wrong target"
            return (← instantiateMVars proof)
          saved.restore
      | none => saved.restore
  throwError "interval_exp_refute: expected a goal `0 ≤ Real.exp x`"

syntax (name := intervalExpRefuteTac) "interval_exp_refute" : tactic

@[tactic intervalExpRefuteTac] meta def evalIntervalExpRefute : Tactic := fun stx => do
  match stx with
  | `(tactic| interval_exp_refute) =>
      let goal ← getMainGoal
      goal.withContext do
        goal.assign (← proveSplitRefute (← instantiateMVars (← goal.getType)))
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

/-- The left branch closes from its split assumption; the right branch uses
its incompatible assumption to derive `.empty`, proves that exact fact
impossible, and only then participates in the parent join. -/
theorem tacticExpRefutedBranch (x : ℝ) : 0 ≤ Real.exp x := by
  interval_exp_refute

/--
info: 'Hex.IntervalMathlib.ExpSignConformance.tacticExpRefutedBranch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms tacticExpRefutedBranch

/-- Failure on an unsupported target restores the tactic state. -/
example (x : ℝ) : x = x := by
  fail_if_success interval_exp_refute
  rfl

set_option linter.unusedTactic false in
example : True := by
  run_tac
    let some result := runRaw? outputRightInput firstOffer
        limits.policy.maxDecisions outputRightScope
      | throwError "interval_exp_refute test: missing contradictory child"
    let .ok registry := ProofRegistry.build result.session.registry proofPackages
      | throwError "interval_exp_refute test: child registry failed"
    let some trace := Frontend.trace? result.session.state.engine result.session.arena
      | throwError "interval_exp_refute test: child quotation failed"
    let state ← ProofFrontend.emitBranch outputRightContext outputRightInput
      (mkConst ``outputRightSeed) trace.program trace.events registry.emit
    let moved := result.session.state.engine.facts.set! 0 .empty
    if (← observing? <| ProofFrontend.refuteCurrent outputRightContext state
        registry.refute moved result.session.state.engine.versions
        outputRightInput.target).isSome then
      throwError "interval_exp_refute test: bottom at an unproved node was accepted"
    let changed := result.session.state.engine.facts.set! 1 .all
    if (← observing? <| ProofFrontend.refuteCurrent outputRightContext state
        registry.refute changed result.session.state.engine.versions
        outputRightInput.target).isSome then
      throwError "interval_exp_refute test: changed bottom fact was accepted"
    let stale := result.session.state.engine.versions.set! 1 0
    if (← observing? <| ProofFrontend.refuteCurrent outputRightContext state
        registry.refute result.session.state.engine.facts stale
        outputRightInput.target).isSome then
      throwError "interval_exp_refute test: stale bottom version was accepted"
  trivial

/-! ## Branch-dependent ReLU propagation

Unlike exponential positivity, these two propagators are intentionally
conditional.  The nonnegative-side rule proves the output fact by rewriting
with `max x 0 = x` from `0 <= x`; the negative-side rule does so by rewriting
with `max x 0 = 0` from `x < 0`.  This conditionality is a package-test design
choice for an unconditional final theorem.  The runtime and proof packages
know those two function-specific facts, while branch creation, branch seeding,
chronology replay, and the two-proof join stay generic. -/

private def reluKey : OpKey := { name := "relu-sign.max-zero" }

private def reluNonnegativeKey : RuleKey :=
  { name := "relu-sign.max-zero.nonnegative" }

private def reluNegativeKey : RuleKey :=
  { name := "relu-sign.max-zero.negative" }

private def reluOperation : Operation :=
  { key := reluKey, inputs := [real], output := real }

private def reluOperations : Array Operation := #[sourceOperation, reluOperation]

private def reluInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }

private def reluProgram : Program :=
  { operations := reluOperations, nodes := #[sourceInstruction, reluInstruction] }

private def reluNonnegativeRule : Registration :=
  { key := reluNonnegativeKey
    head := reluKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

private def reluNegativeRule : Registration :=
  { key := reluNegativeKey
    head := reluKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

private def reluFormat (side : Bound) : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body => body == [side.code] }

private def reluPlan (side : Bound) (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [source], [target] =>
      if source.fact == side then
        { outcome :=
            .success
              [{ node := target, fact := .nonnegative, payload := payload 0 }]
              [] {}
          drafts :=
            [{ label := payload 0
               role := .fact
               schema := 1
               body := [side.code] }] }
      else
        { outcome := .failed 10, drafts := [] }
  | _, _ => { outcome := .failed 11, drafts := [] }

private def reluPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[reluOperation]
    handlers :=
      #[Handler.statelessPlanned reluNonnegativeRule
          (reluPlan .nonnegative) #[reluFormat .nonnegative],
        Handler.statelessPlanned reluNegativeRule
          (reluPlan .negative) #[reluFormat .negative]] }

private def reluPackages : Array (Package Bound) := #[sourcePackage, reluPackage]

private def reluSplitPackages : Array (Package Bound) :=
  #[sourcePackage, reluPackage, splitPackage]

private def reluModel : OperationSemantics.Model ℝ :=
  { operation := reluOperation
    relation := fun inputs output =>
      match inputs with
      | [input] => output = max input 0
      | _ => False }

private def reluModels : Array (OperationSemantics.Model ℝ) :=
  #[sourceModel, reluModel]

private def reluSemantics : Semantics Bound :=
  OperationSemantics.semantics reluModels Contains

private def reluBoundSchema : FactDomainSchema reluSemantics :=
  { top := fun _ => .all
    topSound := by
      intro _ _ _ _ _ _
      trivial
    proveMeet := fun _ _ previous proposed installed =>
      if exact : installed = previous.meet proposed then
        some
          { proof := by
              subst installed
              intro valuation _
              exact containsMeet previous proposed (valuation _) }
      else
        none }

private def reluLaws : Laws reluSemantics :=
  { holdsEq := by
      intro _ valuation left right fact _ _ values
      change Contains fact (valuation left) ↔ Contains fact (valuation right)
      rw [values] }

private def reluStableLaw : GenericInstanceReconstruction.StableLaw reluSemantics :=
  OperationSemantics.stableLaw reluModels Contains

private def reluSplitSchema : SplitSchema reluSemantics Unit where
  proveCover := fun _ _ parent _ left right =>
    if shape : parent = .all ∧ left = .nonnegative ∧ right = .negative then
      some
        { proof := by
            rcases shape with ⟨rfl, rfl, rfl⟩
            intro valuation _ _
            change NodeId → ℝ at valuation
            change (0 : ℝ) ≤ valuation _ ∨ valuation _ < 0
            exact le_or_gt 0 (valuation _) }
    else
      none

private theorem reluSideEntails (side : Bound)
    (accepted : side = .nonnegative ∨ side = .negative)
    (graph : Program) (assumptions : List (NodeFact Bound))
    (output : NodeId) (instruction : Node) (input : NodeId)
    (found : graph.node? output = some instruction)
    (operation : instruction.op = { index := 1 })
    (arguments : instruction.args = [input])
    (exactAssumptions : assumptions = [{ node := input, fact := side }]) :
    reluSemantics.Entails graph assumptions
      { node := output, fact := .nonnegative } := by
  change ∀ valuation : NodeId → ℝ,
    OperationSemantics.Models reluModels graph valuation →
      (∀ assumption, assumption ∈ assumptions →
        Contains assumption.fact (valuation assumption.node)) →
      Contains .nonnegative (valuation output)
  intro valuation model holds
  obtain ⟨meaning, meaningAt, related⟩ :=
    model.2 output instruction found
  simp [reluModels, operation] at meaningAt
  subst meaning
  have outputEq : valuation output = max (valuation input) 0 := by
    simpa [reluModel, arguments, List.map] using related
  have inputH : Contains side (valuation input) :=
    holds { node := input, fact := side } (by simp [exactAssumptions])
  rcases accepted with rfl | rfl
  · change (0 : ℝ) ≤ valuation output
    rw [outputEq, max_eq_left inputH]
    exact inputH
  · change (0 : ℝ) ≤ valuation output
    change valuation input < 0 at inputH
    rw [outputEq, max_eq_right inputH.le]

private theorem reluFactWith (fact : NodeFact Bound) {value : Bound}
    (equal : fact.fact = value) :
    fact = { node := fact.node, fact := value } := by
  cases fact
  simp_all

private def reluFactSchema (key : RuleKey) (side : Bound)
    (accepted : side = .nonnegative ∨ side = .negative) :
    PackedFactSchema reluSemantics where
  rule := key
  schema := 1
  Certificate := Unit
  decode := fun body => if body == [side.code] then some () else none
  replay := fun _ _ context _ =>
    if proposedFact : context.proposed.fact = .nonnegative then
      match found : context.program.node? context.proposed.node with
      | some instruction =>
          if operation : instruction.op = ({ index := 1 } : OpId) then
            match arguments : instruction.args with
            | [input] =>
                if exactAssumptions :
                    context.assumptions = [{ node := input, fact := side }] then
                  some
                    { proof := by
                        have proposedEq :
                            context.proposed =
                              { node := context.proposed.node,
                                fact := .nonnegative } :=
                          reluFactWith context.proposed proposedFact
                        rw [proposedEq]
                        exact
                          reluSideEntails side accepted context.program
                            context.assumptions context.proposed.node instruction
                            input found operation arguments exactAssumptions }
                else
                  none
            | _ => none
          else
            none
      | none => none
    else
      none

private def reluNonnegativeSchema : PackedFactSchema reluSemantics :=
  reluFactSchema reluNonnegativeKey .nonnegative (Or.inl rfl)

private def reluNegativeSchema : PackedFactSchema reluSemantics :=
  reluFactSchema reluNegativeKey .negative (Or.inr rfl)

private def reluSourceProof : ProofRegistry.Package reluSemantics Name :=
  { semantic := { factSchemas := #[] }
    emit := { schemas := [] } }

private def reluProof : ProofRegistry.Package reluSemantics Name :=
  { semantic :=
      { factSchemas := #[reluNonnegativeSchema, reluNegativeSchema] }
    emit :=
      { schemas :=
          [{ key := reluNonnegativeSchema.key,
             handle := ``reluNonnegativeSchema },
           { key := reluNegativeSchema.key,
             handle := ``reluNegativeSchema }] } }

private def reluProofPackages :
    Array (ProofRegistry.Package reluSemantics Name) :=
  #[reluSourceProof, reluProof]

private def reluBaseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .all }, { node := node 1, fact := .all }]

private def reluInput : CheckerInput Bound :=
  { baseProgram := reluProgram
    initialFacts := #[.all, .all]
    target := { node := node 1, fact := .nonnegative } }

private theorem reluBaseWithin : FactsWithin reluProgram reluBaseFacts := by
  intro fact member
  simp only [reluBaseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [reluProgram, node]

private theorem reluBasePrefix : ProgramPrefix reluProgram reluProgram :=
  ProgramPrefix.refl reluProgram

private theorem reluSameOperations :
    reluProgram.operations = reluProgram.operations := rfl

private def reluInitialExtension :
    Evidence (reluSemantics.Extends reluProgram reluProgram) :=
  extendRefl reluSemantics reluProgram

private noncomputable def reluValuation (x : ℝ) : NodeId → ℝ
  | ⟨0⟩ => x
  | ⟨1⟩ => max x 0
  | _ => 0

private theorem reluValuationModels (x : ℝ) :
    reluSemantics.models reluProgram (reluValuation x) := by
  refine ⟨?_, ?_⟩
  · simp [reluProgram, reluOperations, reluModels, sourceModel, reluModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, reluProgram, sourceInstruction] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, reluProgram, reluInstruction] at found
          subst instruction
          exact ⟨reluModel, by rfl, by rfl⟩
      | succ index =>
          simp [Program.node?, reluProgram] at found

private theorem closeRelu (x : ℝ)
    (result : Evidence
      (reluSemantics.Entails reluProgram reluBaseFacts reluInput.target)) :
    0 ≤ max x 0 := by
  have holds := result.proof (reluValuation x) (reluValuationModels x)
    (by
      intro fact member
      simp only [reluBaseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> trivial)
  exact holds

private def reluOffer? (key : RuleKey) (view : Propagator.Policy.View Bound) :
    Option Propagator.Policy.OfferView :=
  view.offers.toList.find? fun offer =>
    match offer.key with
    | .invoke invocation => invocation.rule == key
    | _ => false

private def reluRulePolicy (key : RuleKey) :
    TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match reluOffer? key view with
      | some offer => .select offer state
      | none => .stop state }

private def reluRunWith? (runtimePackages : Array (Package Bound))
    (input : CheckerInput Bound) (controller : TargetRun.Controller Bound Unit)
    (scope : Propagator.Policy.ScopeId := { index := 0 }) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain
      input.baseProgram runtimePackages input.initialFacts limits scope
    | none
  some (TargetRun.drive factDomain input.target.node input.target.fact controller
    limits.policy.maxDecisions session ())

private def reluPrepared? :
    Option (ULift.{1, 0} (BranchStart.Children Bound)) :=
  match reluRunWith? reluSplitPackages reluInput splitPolicy with
  | none => none
  | some result =>
      match result.stop with
      | .split plan =>
          match BranchStart.prepare branchLimits
              (BranchStart.State.start result.session) result.session plan
              reluInput.target signSplitter with
          | .ok (_, children) => some (ULift.up children)
          | .error _ => none
      | _ => none

private def reluBranchFact (side : Bound) : NodeFact Bound :=
  { node := node 0, fact := side }

private def reluBranchFacts (side : Bound) : List (NodeFact Bound) :=
  reluBranchFact side :: reluBaseFacts

private def reluBranchInput (side : Bound) : CheckerInput Bound :=
  { baseProgram := reluProgram
    initialFacts := #[side, .all]
    target := reluInput.target }

private def reluInherit (side : Bound) (observed : NodeId)
    (different : observed ≠ node 0) (fact : Bound)
    (found : (reluBranchInput side).initialFacts[observed.index]? = some fact) :
    Evidence
      (reluSemantics.Entails reluProgram reluBaseFacts { node := observed, fact }) :=
  { proof := by
      intro _ _ assumptions
      cases observed with
      | mk index =>
          cases index with
          | zero => simp [node] at different
          | succ index =>
              cases index with
              | zero =>
                  simp [reluBranchInput] at found
                  subst fact
                  exact assumptions _ (by simp [reluBaseFacts, node])
              | succ index => simp [reluBranchInput] at found }

private def reluLeftInput : CheckerInput Bound :=
  reluBranchInput .nonnegative

private def reluRightInput : CheckerInput Bound :=
  reluBranchInput .negative

private def reluLeftFacts : List (NodeFact Bound) :=
  reluBranchFacts .nonnegative

private def reluRightFacts : List (NodeFact Bound) :=
  reluBranchFacts .negative

private def reluLeftSeed :
    ProofEmitter.BranchSeed reluSemantics reluLeftInput reluBaseFacts
      (reluBranchFact .nonnegative) :=
  ProofEmitter.BranchSeed.make reluLeftInput (reluBranchFact .nonnegative)
    (by rfl) (by rfl) (reluInherit .nonnegative)

private def reluRightSeed :
    ProofEmitter.BranchSeed reluSemantics reluRightInput reluBaseFacts
      (reluBranchFact .negative) :=
  ProofEmitter.BranchSeed.make reluRightInput (reluBranchFact .negative)
    (by rfl) (by rfl) (reluInherit .negative)

private structure ReluRun where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry reluSemantics Name
  reached : TargetRun.Reached Bound

private def reluRunChild? (side : Bound) (input : CheckerInput Bound)
    (scope : Propagator.Policy.ScopeId) : Option ReluRun := do
  let key := if side == .nonnegative then reluNonnegativeKey else reluNegativeKey
  let result ← reluRunWith? reluPackages input (reluRulePolicy key) scope
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry reluProofPackages
    | none
  some { session := result.session, registry, reached }

#guard
  reluPrepared?.any fun lifted =>
    let children := lifted.down
    children.depth == 1 && sameChecker children.parent reluInput &&
      children.leftScope == ({ index := 1 } : Propagator.Policy.ScopeId) &&
      children.rightScope == ({ index := 2 } : Propagator.Policy.ScopeId) &&
      sameChecker children.left reluLeftInput &&
      sameChecker children.right reluRightInput

private def reluTraceUses? (side : Bound) (input : CheckerInput Bound)
    (scope : Propagator.Policy.ScopeId) : Bool :=
  match reluRunChild? side input scope with
  | none => false
  | some run =>
      match Frontend.trace? run.session.state.engine run.session.arena with
      | some trace =>
          match trace.events with
          | [.rule step] =>
              trace.program == input.baseProgram &&
                run.reached.seen ==
                  ({ node := node 1, version := 1 } : SeenVersion) &&
                run.reached.fact == .nonnegative &&
                run.session.state.engine.facts == #[side, .nonnegative] &&
                run.session.state.engine.versions == #[0, 1] &&
                step.assumptions == [reluBranchFact side] &&
                step.event.programVersion == 0 && step.event.node == node 1 &&
                step.event.previous ==
                  ({ node := node 1, version := 0 } : SeenVersion) &&
                step.event.fact == .nonnegative &&
                step.event.version == 1 && step.previous == .all &&
                step.entry.replayKey ==
                  (if side == .nonnegative then reluNonnegativeSchema.key
                   else reluNegativeSchema.key)
          | _ => false
      | none => false

#guard reluTraceUses? .nonnegative reluLeftInput { index := 1 }
#guard reluTraceUses? .negative reluRightInput { index := 2 }

private def reluRejectsUnsplit? (key : RuleKey) : Bool :=
  reluRunWith? reluPackages reluInput (reluRulePolicy key) |>.any fun result =>
    (match result.stop with | .target _ => false | _ => true) &&
      result.session.state.engine.facts == #[.all, .all] &&
      result.session.state.engine.history.isEmpty

#guard reluRejectsUnsplit? reluNonnegativeKey
#guard reluRejectsUnsplit? reluNegativeKey

private theorem reluBranchWithin (side : Bound) :
    FactsWithin reluProgram (reluBranchFacts side) := by
  intro fact member
  simp only [reluBranchFacts, reluBranchFact, reluBaseFacts, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [reluProgram, node]

private def reluSeedAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence (reluSemantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def reluContext (input facts within : Expr)
    (factValues : List (NodeFact Bound)) : ProofFrontend.Context Bound Name :=
  { encoder := boundEncoder
    resolveSchema := pure
    semantics := mkConst ``reluSemantics
    domain := mkConst ``reluBoundSchema
    laws := mkConst ``reluLaws
    stableLaw := mkConst ``reluStableLaw
    input
    assumed := ``reluSeedAssumed
    baseFacts := factValues
    baseFactsTerm := facts
    baseProgram := reluProgram
    baseProgramTerm := mkConst ``reluProgram
    basePrefix := mkConst ``reluBasePrefix
    baseWithin := within
    initialExtension := mkConst ``reluInitialExtension
    finalPrefix := mkConst ``reluBasePrefix
    sameOperations := mkConst ``reluSameOperations
    top := reluBoundSchema.top }

private def reluLeftContext : ProofFrontend.Context Bound Name :=
  reluContext (mkConst ``reluLeftInput) (mkConst ``reluLeftFacts)
    (mkApp (mkConst ``reluBranchWithin) (mkConst ``Bound.nonnegative))
    reluLeftFacts

private def reluRightContext : ProofFrontend.Context Bound Name :=
  reluContext (mkConst ``reluRightInput) (mkConst ``reluRightFacts)
    (mkApp (mkConst ``reluBranchWithin) (mkConst ``Bound.negative))
    reluRightFacts

private def reluParent : Evidence
    (reluSemantics.Entails reluProgram reluBaseFacts (reluBranchFact .all)) :=
  ProofEmitter.assumed (by simp [reluBaseFacts, reluBranchFact, node])

private meta def emitReluChild (context : ProofFrontend.Context Bound Name)
    (side : Bound) (input : CheckerInput Bound)
    (scope : Propagator.Policy.ScopeId) (seed : Expr) : MetaM Expr := do
  let some run := reluRunChild? side input scope
    | throwError "interval_relu_split: child search failed"
  let some trace := Frontend.trace? run.session.state.engine run.session.arena
    | throwError "interval_relu_split: child chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "interval_relu_split: child trace is not exactly one rule"
  let expectedKey :=
    if side == .nonnegative then reluNonnegativeSchema.key
    else reluNegativeSchema.key
  unless trace.program == input.baseProgram &&
      run.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      run.reached.fact == .nonnegative &&
      run.session.state.engine.facts == #[side, .nonnegative] &&
      run.session.state.engine.versions == #[0, 1] &&
      step.assumptions == [reluBranchFact side] &&
      step.event.programVersion == 0 && step.event.node == node 1 &&
      step.event.previous == ({ node := node 1, version := 0 } : SeenVersion) &&
      step.event.fact == .nonnegative && step.event.version == 1 &&
      step.previous == .all && step.entry.replayKey == expectedKey do
    throwError "interval_relu_split: child result or quoted rule trace drifted"
  let state ← ProofFrontend.emitBranch context input seed trace.program
    trace.events run.registry.emit
  ProofFrontend.closeTarget context state run.reached.seen run.reached.fact input.target

private meta def emitReluSplit : MetaM Expr := do
  let some lifted := reluPrepared?
    | throwError "interval_relu_split: branch preparation failed"
  let children := lifted.down
  let left ← emitReluChild reluLeftContext .nonnegative children.left
    children.leftScope (mkConst ``reluLeftSeed)
  let right ← emitReluChild reluRightContext .negative children.right
    children.rightScope (mkConst ``reluRightSeed)
  let result ←
    mkAppM ``ProofEmitter.replaySplit
      #[mkConst ``reluSplitSchema, mkConst ``reluProgram,
        mkConst ``reluBaseFacts, ← boundEncoder.nodeId (node 0),
        ← boundEncoder.fact .all, mkConst ``Unit.unit,
        ← boundEncoder.fact .nonnegative, ← boundEncoder.fact .negative,
        ← boundEncoder.nodeFact reluInput.target,
        mkConst ``reluParent, left, right]
  ProofFrontend.replayResult result

/-- The emitted term contains both live child replays and the checked generic
split join.  Assigning that term to this declaration makes the ordinary kernel,
not the Meta evaluator, validate the complete proof. -/
private def reluJoined : Evidence
    (reluSemantics.Entails reluProgram reluBaseFacts reluInput.target) := by
  run_tac
    let goal ← getMainGoal
    goal.assign (← emitReluSplit)

/-- An arbitrary-function vertical whose child proofs consume distinct split
assumptions by construction: neither ReLU propagator fires before the zero
split.  The final theorem is unconditional; conditionality here tests the
branch proof plumbing rather than mathematical necessity. -/
theorem reluSplit (x : ℝ) : 0 ≤ max x 0 :=
  closeRelu x reluJoined

/--
info: 'Hex.IntervalMathlib.ExpSignConformance.reluSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reluSplit

set_option linter.unusedTactic false in
example : True := by
  run_tac
    let checkMutation (context : ProofFrontend.Context Bound Name)
        (side wrong : Bound) (input : CheckerInput Bound)
        (scope : Propagator.Policy.ScopeId) (seed : Expr) : MetaM Unit := do
      let some run := reluRunChild? side input scope
        | throwError "interval_relu_split mutation: child search failed"
      let some trace := Frontend.trace? run.session.state.engine run.session.arena
        | throwError "interval_relu_split mutation: trace missing"
      let [.rule step] := trace.events
        | throwError "interval_relu_split mutation: wrong trace shape"
      let mutated : RuleStep Bound :=
        { step with assumptions := [reluBranchFact wrong] }
      if (← observing? <| ProofFrontend.emitBranch context input seed trace.program
          [.rule mutated] run.registry.emit).isSome then
        throwError
          "interval_relu_split mutation: opposite split assumption was accepted"
    checkMutation reluLeftContext .nonnegative .negative reluLeftInput
      { index := 1 } (mkConst ``reluLeftSeed)
    checkMutation reluRightContext .negative .nonnegative reluRightInput
      { index := 2 } (mkConst ``reluRightSeed)
  trivial

end Hex.IntervalMathlib.ExpSignConformance
