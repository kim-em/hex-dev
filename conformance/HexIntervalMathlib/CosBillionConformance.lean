/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.CosBillion
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Huge-argument cosine replay conformance

The runtime authenticates a large integer quotient and rational residual
window before the generic chronology and proof frontend reconstruct the
ordinary theorem `0 < Real.cos (10^10)`.
-/

namespace Hex.IntervalMathlib.CosBillionConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend FrontendEncoder ProofFrontend ProofRegistry
open Hex.Interval.Experiment.CosBillion
open Hex.IntervalMathlib.Experiment.CosBillion

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

private def fixture? : Option Fixture := do
  let .ok session := Session.start factDomain checkerInput.baseProgram packages
      checkerInput.initialFacts limits
    | none
  let result := TargetRun.drive factDomain checkerInput.target.node
    checkerInput.target.fact firstOffer limits.policy.maxDecisions session ()
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { result, reached, registry }

#guard fixture?.isSome

#guard fixture?.any fun fixture =>
  fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
    fixture.reached.fact == positiveFact &&
    fixture.result.session.state.engine.facts ==
      #[.all, positiveFact, finePiFact, residualFact, negativeFact, positiveFact] &&
    fixture.result.session.state.engine.chronology ==
      #[.fact 0, .fact 1, .fact 2, .fact 3, .instance 0, .fact 4] &&
    fixture.registry.emit.find? reductionSchema.key == some ``reductionSchema &&
    fixture.registry.emit.find? identityEqualitySchema.key ==
      some ``identityEqualitySchema

private def trace? : Option (Frontend.Trace Bound) :=
  match fixture? with
  | none => none
  | some fixture =>
      Frontend.trace? fixture.result.session.state.engine fixture.result.session.arena

private def exactRule (step : RuleStep Bound) (expected : RuleKey) : Bool :=
  match step.event.cause with
  | .rule action _ _ => action.key == expected
  | .transport _ _ => false

private def exactInput (step : RuleStep Bound) (expected : List SeenVersion) : Bool :=
  match step.event.cause with
  | .rule action _ _ => action.inputs == expected
  | .transport _ _ => false

#guard trace?.any fun trace =>
  trace.program == program &&
    match trace.events with
    | [.rule constant, .rule reduction, .rule localCosine,
        .rule negation, .instantiation identity, .transport transport] =>
        constant.event.node == node 2 && constant.event.fact == finePiFact &&
          constant.entry.body == [1] && exactRule constant constantRuleKey &&
          exactInput constant [] &&
        reduction.event.node == node 3 && reduction.event.fact == residualFact &&
          reduction.entry.body == reductionBody reductionCertificate &&
          exactRule reduction reductionRuleKey &&
          exactInput reduction [{ node := node 0, version := 0 },
            { node := node 2, version := 1 }] &&
        localCosine.event.node == node 4 &&
          localCosine.event.fact == negativeFact &&
          localCosine.entry.body == [3] &&
          exactRule localCosine localRuleKey &&
          exactInput localCosine [{ node := node 3, version := 1 }] &&
        negation.event.node == node 5 && negation.event.fact == positiveFact &&
          negation.entry.body == [4] && exactRule negation negationRuleKey &&
          exactInput negation [{ node := node 4, version := 1 }] &&
        identity.event.newNodes.isEmpty &&
          identity.event.newEqualities == [{ index := 0 }] &&
          identity.entry.body == [quotient] &&
        transport.event.node == node 1 && transport.event.fact == positiveFact &&
          transport.entry.body == [quotient]
    | _ => false

private def reductionAction : Action :=
  { serial := 0
    programVersion := 0
    rule := { index := 0 }
    application := { index := 0 }
    key := reductionRuleKey
    node := node 3
    kind := .forward
    effort := 0
    inputs := []
    writes := [node 3] }

private def reductionContext : RuleFactContext checkerInput reductionAction :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions :=
      [{ node := node 0, fact := .all }, { node := node 2, fact := finePiFact }]
    proposed := { node := node 3, fact := residualFact } }

private def wrongQuotient : ReductionCertificate :=
  { reductionCertificate with quotient := quotient - 1 }

private def wrongRemainder : ReductionCertificate :=
  { reductionCertificate with lowerNumerator := 14 }

-- Both mutations are structurally valid payloads.  Their numeric contents,
-- rather than an accidental parser failure, make semantic replay reject them.
#guard (decodeReduction? (reductionBody wrongQuotient)).isSome
#guard (decodeReduction? (reductionBody wrongRemainder)).isSome
#guard (reductionSchema.replay checkerInput reductionAction reductionContext
  wrongQuotient).isNone
#guard (reductionSchema.replay checkerInput reductionAction reductionContext
  wrongRemainder).isNone
#guard (reductionSchema.replay checkerInput reductionAction reductionContext
  reductionCertificate).isSome

private def boundExpr? : Bound → Option Expr
  | .all => some (mkConst ``Bound.all)
  | fact =>
      if fact == finePiFact then some (mkConst ``finePiFact)
      else if fact == residualFact then some (mkConst ``residualFact)
      else if fact == positiveFact then some (mkConst ``positiveFact)
      else if fact == negativeFact then some (mkConst ``negativeFact)
      else none

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) fun fact =>
    match boundExpr? fact with
    | some expression => pure expression
    | none => throwError "cos-billion: unrecognized endpoint fact"

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
    finalPrefix := mkConst ``programPrefix
    sameOperations := mkConst ``sameOperations
    top := boundSchema.top }

private meta def emitEvidence : MetaM Expr := do
  let some fixture := fixture?
    | throwError "cos-billion: search or proof registry failed"
  let some trace := Frontend.trace? fixture.result.session.state.engine
      fixture.result.session.arena
    | throwError "cos-billion: chronology quotation failed"
  unless trace.program == program do
    throwError "cos-billion: unexpected instantiated graph"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  let final ← ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target
  mkAppM ``closeEvidence #[final]

syntax (name := intervalCosBillionTac) "interval_cos_billion" : tactic

@[tactic intervalCosBillionTac] meta def evalIntervalCosBillion : Tactic := fun stx => do
  match stx with
  | `(tactic| interval_cos_billion) =>
      let goal ← getMainGoal
      goal.withContext do
        let evidence ← emitEvidence
        let proof ← mkAppM ``Evidence.proof
          #[evidence, mkConst ``valuation, mkConst ``valuationModels, mkConst ``baseHolds]
        unless ← isDefEq (← inferType proof) (← goal.getType) do
          throwError "cos-billion: emitted proof has the wrong target"
        goal.assign (← instantiateMVars proof)
        replaceMainGoal []
  | _ => throwUnsupportedSyntax

private theorem endpointFact : Contains positiveFact (Real.cos (10 ^ 10)) := by
  interval_cos_billion

/-- A large-argument range-reduction certificate replayed through the generic
package/session/proof frontend establishes the sign of the original cosine. -/
theorem cosBillionPositive : 0 < Real.cos (10 ^ 10) := by
  have enclosure : 0 < Real.cos (10 ^ 10) ∧ Real.cos (10 ^ 10) ≤ 1 := by
    simpa [Contains, positiveFact, rat, ratValue] using endpointFact
  exact enclosure.1

/--
info: 'Hex.IntervalMathlib.CosBillionConformance.cosBillionPositive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cosBillionPositive

end Hex.IntervalMathlib.CosBillionConformance
