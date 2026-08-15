/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalAlgebraic.Experiment.PolynomialDispatchProof
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Specialized polynomial dispatch conformance

The runtime recognizes polynomial expression subgraphs by operation key and
delegates them to `hex-real-roots` or `hex-roots`.  These canaries require both
the actual backend result and its Mathlib correspondence theorem before the
generic proof frontend can construct evidence.
-/

namespace Hex.IntervalAlgebraic.PolynomialDispatchConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ProofEmitter ProofRegistry Frontend
open Hex.Interval.Experiment.PolynomialDispatch

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? (selected : Array (Package Bound)) (input : CheckerInput Bound) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := Session.start factDomain input.baseProgram selected
      input.initialFacts limits | none
  some (TargetRun.drive factDomain input.target.node input.target.fact firstOffer
    limits.policy.maxDecisions session ())

structure RealFixture where
  session : Session Bound
  registry : Registry realSemantics Name
  reached : TargetRun.Reached Bound

structure ComplexFixture where
  session : Session Bound
  registry : Registry complexSemantics Name
  reached : TargetRun.Reached Bound

private def realFixture? : Option RealFixture := do
  let result ← run? realPackages realCheckerInput
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry realProofPackages | none
  some ⟨result.session, registry, reached⟩

private def complexFixture? : Option ComplexFixture := do
  let result ← run? complexPackages complexCheckerInput
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry complexProofPackages | none
  some ⟨result.session, registry, reached⟩

#guard realFixture?.any fun fixture =>
  fixture.reached.seen == ({ node := node 5, version := 1 } : SeenVersion) &&
    fixture.reached.fact == .cubeTwoReal &&
    fixture.registry.emit.find? realFactSchema.key == some ``realFactSchema

#guard complexFixture?.any fun fixture =>
  fixture.reached.seen == ({ node := node 6, version := 1 } : SeenVersion) &&
    fixture.reached.fact == .pisotComplex &&
    fixture.registry.emit.find? complexFactSchema.key == some ``complexFactSchema

/-! ## Recognition and backend mutation rejection -/

private def view (program : Program) : ProgramView :=
  { programVersion := 0
    operations := program.operations
    nodes := program.nodes
    generations := Array.replicate program.nodes.size 0
    depths := Array.replicate program.nodes.size 0 }

private def request (program : Program) (target : NodeId) (rule : RuleKey)
    (ruleIndex : Nat) : RuleRequest Bound :=
  { action :=
      { serial := 0, programVersion := 0, application := { index := 0 }
        rule := { index := ruleIndex }, key := rule, node := target
        kind := .forward, effort := 0, generation := 0, inputs := []
        writes := [target] }
    program := view program
    inputs := []
    writes := [target] }

private def declines (plan : Plan Bound) : Bool :=
  match plan.outcome with | .noChange _ => true | _ => false

private def nonPolynomialProgram : Program :=
  { realProgram with nodes := realProgram.nodes.set! 4 (instruction 7 [node 3]) }

private def variableMutation : Program :=
  { realProgram with nodes := realProgram.nodes.set! 0 (instruction 1) }

private def orderMutation : Program :=
  { realProgram with
    nodes := realProgram.nodes.set! 4 (instruction 5 [node 1, node 3]) }

private def coefficientMutation : Program :=
  { realProgram with nodes := realProgram.nodes.set! 1 (instruction 2) }

#guard declines (realPlan (request nonPolynomialProgram (node 5) realRuleKey 0))
#guard declines (realPlan (request variableMutation (node 5) realRuleKey 0))
#guard declines (realPlan (request orderMutation (node 5) realRuleKey 0))
#guard declines (realPlan (request coefficientMutation (node 5) realRuleKey 0))

-- Both checks below execute the specialized algorithms, rather than accepting
-- a preinstalled theorem or a shape-only provider answer.
#guard realResultMatches (realBackend? cubeTwo 4)
#guard complexResultMatches (complexBackend? pisot 32)

#guard (decodeReal? realBody).isSome
#guard (decodeReal? (realBody.set 2 1)).isNone
#guard (decodeReal? (realBody.set 10 15)).isNone
#guard (decodeComplex? complexBody).isSome
#guard (decodeComplex? (complexBody.set 8 182067849688)).isNone

/-! ## Semantic replay cannot be bypassed -/

private def realAction : Action :=
  { serial := 0, programVersion := 0, application := { index := 0 }
    rule := { index := 0 }, key := realRuleKey, node := node 5
    kind := .forward, effort := 0, generation := 0, inputs := [], writes := [node 5] }

private def complexAction : Action :=
  { serial := 0, programVersion := 0, application := { index := 0 }
    rule := { index := 1 }, key := complexRuleKey, node := node 6
    kind := .forward, effort := 0, generation := 0, inputs := [], writes := [node 6] }

private def realContext : RuleFactContext realCheckerInput realAction :=
  { program := realProgram, basePrefix := ProgramPrefix.refl _
    assumptions := [], proposed := { node := node 5, fact := .cubeTwoReal } }

private def complexContext : RuleFactContext complexCheckerInput complexAction :=
  { program := complexProgram, basePrefix := ProgramPrefix.refl _
    assumptions := [], proposed := { node := node 6, fact := .pisotComplex } }

private def wrongRealInput : CheckerInput Bound :=
  { baseProgram := orderMutation
    initialFacts := Array.replicate orderMutation.nodes.size .all
    target := { node := node 5, fact := .cubeTwoReal } }

private def wrongRealContext : RuleFactContext wrongRealInput realAction :=
  { program := orderMutation, basePrefix := ProgramPrefix.refl _
    assumptions := [], proposed := { node := node 5, fact := .cubeTwoReal } }

#guard (realFactSchema.replay realCheckerInput realAction realContext realCertificate).isSome
#guard (complexFactSchema.replay complexCheckerInput complexAction complexContext
  complexCertificate).isSome
#guard (realFactSchema.replay wrongRealInput realAction wrongRealContext
  realCertificate).isNone
#guard (realFactSchema.decode (realBody.set 2 1)).isNone
#guard (complexFactSchema.decode (complexBody.set 8 182067849688)).isNone

/-! ## Generic frontend and ordinary theorems -/

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .cubeTwoReal => mkConst ``Bound.cubeTwoReal
  | .pisotComplex => mkConst ``Bound.pisotComplex
  | .empty => mkConst ``Bound.empty

private def encoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))

private def realAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence (realSemantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def complexAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence (complexSemantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def realFrontend : ProofFrontend.Context Bound Name :=
  { encoder, resolveSchema := pure, semantics := mkConst ``realSemantics
    domain := mkConst ``realBoundSchema, laws := mkConst ``realLaws
    stableLaw := mkConst ``realStableLaw, input := mkConst ``realCheckerInput
    assumed := ``realAssumed, baseFacts := realBaseFacts
    baseFactsTerm := mkConst ``realBaseFacts, baseProgram := realProgram
    baseProgramTerm := mkConst ``realProgram, basePrefix := mkConst ``realPrefix
    baseWithin := mkConst ``realBaseWithin, initialExtension := mkConst ``realExtension
    finalPrefix := mkConst ``realPrefix, sameOperations := mkConst ``realOperations
    top := realBoundSchema.top }

private def complexFrontend : ProofFrontend.Context Bound Name :=
  { encoder, resolveSchema := pure, semantics := mkConst ``complexSemantics
    domain := mkConst ``complexBoundSchema, laws := mkConst ``complexLaws
    stableLaw := mkConst ``complexStableLaw, input := mkConst ``complexCheckerInput
    assumed := ``complexAssumed, baseFacts := complexBaseFacts
    baseFactsTerm := mkConst ``complexBaseFacts, baseProgram := complexProgram
    baseProgramTerm := mkConst ``complexProgram, basePrefix := mkConst ``complexPrefix
    baseWithin := mkConst ``complexBaseWithin,
    initialExtension := mkConst ``complexExtension, finalPrefix := mkConst ``complexPrefix
    sameOperations := mkConst ``complexOperations, top := complexBoundSchema.top }

private meta def emitReal : MetaM Expr := do
  let some fixture := realFixture? | throwError "real specialized dispatch failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "real specialized chronology failed"
  let state ← ProofFrontend.emitTrace realFrontend trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget realFrontend state fixture.reached.seen fixture.reached.fact
    realCheckerInput.target

private meta def emitComplex : MetaM Expr := do
  let some fixture := complexFixture? | throwError "complex specialized dispatch failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "complex specialized chronology failed"
  let state ← ProofFrontend.emitTrace complexFrontend trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget complexFrontend state fixture.reached.seen fixture.reached.fact
    complexCheckerInput.target

theorem cubeTwoRoots {x : ℝ} (root : x ^ 3 - 2 = 0) :
    (5 : ℝ) / 4 < x ∧ x ≤ 21 / 16 := by
  have evidence : Evidence
      (realSemantics.Entails realProgram realBaseFacts realCheckerInput.target) := by
    run_tac
      let proof ← emitReal
      let goal ← getMainGoal
      unless ← isDefEq (← inferType proof) (← goal.getType) do
        throwError "real specialized evidence has the wrong type"
      goal.assign (← instantiateMVars proof)
      replaceMainGoal []
  exact closeReal evidence root

theorem pisotRoots {z : ℂ} (root : z ^ 3 - z - 1 = 0) :
    z ∈ HexRootsMathlib.DyadicSquare.closedSquare
        HexRootsMathlib.Examples.pisotLowerSquare ∨
      z ∈ HexRootsMathlib.DyadicSquare.closedSquare
        HexRootsMathlib.Examples.pisotUpperSquare ∨
      z ∈ HexRootsMathlib.DyadicSquare.closedSquare
        HexRootsMathlib.Examples.pisotRealSquare := by
  change ComplexContains .pisotComplex z
  have evidence : Evidence
      (complexSemantics.Entails complexProgram complexBaseFacts complexCheckerInput.target) := by
    run_tac
      let proof ← emitComplex
      let goal ← getMainGoal
      unless ← isDefEq (← inferType proof) (← goal.getType) do
        throwError "complex specialized evidence has the wrong type"
      goal.assign (← instantiateMVars proof)
      replaceMainGoal []
  exact closeComplex evidence root

/--
info: 'Hex.IntervalAlgebraic.PolynomialDispatchConformance.cubeTwoRoots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cubeTwoRoots

/--
info: 'Hex.IntervalAlgebraic.PolynomialDispatchConformance.pisotRoots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pisotRoots

end Hex.IntervalAlgebraic.PolynomialDispatchConformance
