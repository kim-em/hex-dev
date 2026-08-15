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
import HexInterval.Experiment.BranchTree
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

local notation "OfferView" =>
  Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "Selection" =>
  Hex.Interval.Policy.Decision _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "ScopeId" => Hex.Interval.Policy.ScopeId
local notation "OfferClass" => Hex.Interval.Policy.OfferClass

open Lean Elab Tactic Meta
open Hex.Interval
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
    (accepts : (Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) → Bool) :
    Option
      ((Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) × (Hex.Interval.Policy.Decision _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) ×
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

def invokesExpAt (target : NodeId) (offer : (Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey)) : Bool :=
  match offer.key with
  | .invoke invocation =>
      invocation.rule == expRuleKey && invocation.anchor == target
  | _ => false

def invokesExp (offer : (Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey)) : Bool :=
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
    (fuel : Nat) (scope : Hex.Interval.Policy.ScopeId := { index := 0 }) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain
      input.baseProgram runtimePackages input.initialFacts limits scope
    | none
  some (TargetRun.drive factDomain input.target.node input.target.fact controller
    fuel session ())

def runRaw? (input : CheckerInput Bound) (controller : TargetRun.Controller Bound Unit)
    (fuel : Nat) (scope : Hex.Interval.Policy.ScopeId := { index := 0 }) :
    Option (TargetRun.Result Bound Unit) :=
  runWith? packages input controller fuel scope

def runInput? (input : CheckerInput Bound)
    (scope : Hex.Interval.Policy.ScopeId := { index := 0 }) : Option RunFixture := do
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

private def splitOffer? (view : (Hex.Interval.Policy.View Bound Propagator.Policy.OfferId Propagator.Policy.OfferKey)) :
    Option (Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) :=
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
private def leftScope : Hex.Interval.Policy.ScopeId := { index := 1 }
private def rightScope : Hex.Interval.Policy.ScopeId := { index := 2 }
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

/-! ## Retained resource-bounded branch trees -/

/-- Split only at the root; in each exact child, select the exponential
propagator.  This deliberately keeps scheduling policy outside the generic
tree manager. -/
private def treePolicy : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      let selected :=
        if view.scope.index == 0 then splitOffer? view
        else view.offers.toList.find? (invokesExpAt (node 1))
      match selected with
      | some offer => .select offer state
      | none => .stop state }

private def treeLimits (maxSteps := 3) (maxSplits := 1)
    (maxLeaves := 2) : BranchTree.Limits :=
  { branch := branchLimits
    maxSteps
    maxSplits
    maxLeaves
    leafFuel := limits.policy.maxDecisions }

private def treeConfig (resources : BranchTree.Limits) :
    BranchTree.Config Bound Unit :=
  { factDomain
    packages := splitPackages
    sessionLimits := limits
    controller := treePolicy
    splitter := signSplitter
    forkPolicy := fun state _ => state
    order := .depthFirst
    limits := resources }

private def runTree? (resources : BranchTree.Limits) :
    Option (BranchTree.State Bound Unit) := do
  let .ok state := BranchTree.start (treeConfig resources) { index := 0 }
      checkerInput () | none
  let .ok state := BranchTree.run (treeConfig resources) state | none
  some state

private def targetLeaf (expectedScope : Nat) (expectedSource : Bound)
    (treeNode : BranchTree.Node Bound Unit) : Bool :=
  match treeNode with
  | .leaf source (.result result) =>
      source.scope.index == expectedScope && source.depth == 1 &&
        source.input.initialFacts == #[expectedSource, .all] &&
        match result.stop with
        | .target reached =>
            reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
              reached.fact == .nonnegative &&
              result.session.state.engine.facts == #[expectedSource, .nonnegative]
        | _ => false
  | _ => false

#guard
  runTree? (treeLimits) |>.any fun state =>
    state.nodes.size == 3 && state.frontier.isEmpty && state.settled &&
      state.steps == 3 && state.splits == 1 && state.leaves == 2 &&
      match state.nodes[0]?, state.nodes[1]?, state.nodes[2]? with
      | some (BranchTree.Node.split source _ children left right),
          some leftNode, some rightNode =>
          source.scope.index == 0 && source.depth == 0 &&
            source.input.baseProgram == checkerInput.baseProgram &&
            source.input.initialFacts == checkerInput.initialFacts &&
            source.input.target == checkerInput.target &&
            children.leftScope.index == 1 &&
            children.rightScope.index == 2 && left.index == 1 && right.index == 2 &&
            targetLeaf 1 .nonnegative leftNode && targetLeaf 2 .negative rightNode
      | _, _, _ => false

/- One global step retains the exact split and both runnable children; it does
not claim that either child or the tree is complete. -/
#guard
  runTree? (treeLimits (maxSteps := 1)) |>.any fun state =>
    state.nodes.size == 3 && state.steps == 1 && state.splits == 1 &&
      state.leaves == 2 && state.frontier == [{ index := 1 }, { index := 2 }] &&
      state.stepLimited (treeLimits (maxSteps := 1)) &&
      match state.nodes[1]?, state.nodes[2]? with
      | some (BranchTree.Node.pending _), some (BranchTree.Node.pending _) => true
      | _, _ => false

#guard
  runTree? (treeLimits (maxSplits := 0)) |>.any fun state =>
    state.nodes.size == 1 && state.frontier.isEmpty && state.splits == 0 &&
      state.leaves == 1 &&
      match state.nodes[0]? with
      | some (BranchTree.Node.leaf _
          (BranchTree.LeafEnd.blocked _ BranchTree.Blocked.splitLimit)) => true
      | _ => false

#guard
  runTree? (treeLimits (maxLeaves := 1)) |>.any fun state =>
    state.nodes.size == 1 && state.frontier.isEmpty && state.splits == 0 &&
      state.leaves == 1 &&
      match state.nodes[0]? with
      | some (BranchTree.Node.leaf _
          (BranchTree.LeafEnd.blocked _ BranchTree.Blocked.leafLimit)) => true
      | _ => false

#guard
  BranchTree.schedule .depthFirst [{ index := 9 }]
      [{ index := 1 }, { index := 2 }] ==
    [{ index := 1 }, { index := 2 }, { index := 9 }]

#guard
  BranchTree.schedule .breadthFirst [{ index := 9 }]
      [{ index := 1 }, { index := 2 }] ==
    [{ index := 9 }, { index := 1 }, { index := 2 }]

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
    (input : CheckerInput Bound) (scope : Hex.Interval.Policy.ScopeId)
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

private def outputSplitOffer? (view : (Hex.Interval.Policy.View Bound Propagator.Policy.OfferId Propagator.Policy.OfferKey)) :
    Option (Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) :=
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
private def outputLeftScope : Hex.Interval.Policy.ScopeId := { index := 1 }
private def outputRightScope : Hex.Interval.Policy.ScopeId := { index := 2 }

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
    (scope : Hex.Interval.Policy.ScopeId) : MetaM Expr := do
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
    (scope : Hex.Interval.Policy.ScopeId) : MetaM Expr := do
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

end Hex.IntervalMathlib.ExpSignConformance
