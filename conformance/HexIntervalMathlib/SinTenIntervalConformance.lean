/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.SinTenInterval
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Endpoint-valued `sin 10` replay conformance

The fixed canary drives four package-owned fact steps plus structural
instantiation through the generic runtime chronology and proof frontend.
-/

namespace Hex.IntervalMathlib.SinTenIntervalConformance

open Lean Elab Tactic Meta
open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend FrontendEncoder ProofFrontend ProofRegistry
open Hex.Interval.Experiment.SinTenInterval
open Hex.IntervalMathlib.Experiment.SinTenInterval

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
#guard (constantSchema.decode [2]).isNone
#guard (reductionSchema.decode [3]).isNone
#guard (localSchema.decode [4]).isNone
#guard (negationSchema.decode [3]).isNone
#guard (identityInstanceSchema.decode [0]).isNone
#guard (identityEqualitySchema.decode [0]).isNone

private def boundExpr? : Bound → Option Expr
  | .all => some (mkConst ``Bound.all)
  | fact =>
      if fact == piFact then some (mkConst ``piFact)
      else if fact == residualFact then some (mkConst ``residualFact)
      else if fact == positiveFact then some (mkConst ``positiveFact)
      else if fact == negativeFact then some (mkConst ``negativeFact)
      else none

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) fun fact =>
    match boundExpr? fact with
    | some expression => pure expression
    | none => throwError "sin-ten interval: unrecognized endpoint fact"

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
    baseProgram
    baseProgramTerm := mkConst ``baseProgram
    basePrefix := mkConst ``basePrefix
    baseWithin := mkConst ``baseWithin
    initialExtension := mkConst ``initialExtension
    finalPrefix := mkConst ``programPrefix
    sameOperations := mkConst ``sameOperations
    top := boundSchema.top }

private meta def emitEvidence : MetaM Expr := do
  let some fixture := fixture?
    | throwError "sin-ten interval: search or proof registry failed"
  let some trace := Frontend.trace? fixture.result.session.state.engine
      fixture.result.session.arena
    | throwError "sin-ten interval: chronology quotation failed"
  unless trace.program == extendedProgram do
    throwError "sin-ten interval: unexpected instantiated graph"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  let final ← ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target
  mkAppM ``closeEvidence #[state.extension, final]

syntax (name := intervalSinTenTac) "interval_sin_ten" : tactic

@[tactic intervalSinTenTac] meta def evalIntervalSinTen : Tactic := fun stx => do
  match stx with
  | `(tactic| interval_sin_ten) =>
      let goal ← getMainGoal
      goal.withContext do
        let evidence ← emitEvidence
        let proof ← mkAppM ``Evidence.proof
          #[evidence, mkConst ``valuation, mkConst ``valuationModels, mkConst ``baseHolds]
        unless ← isDefEq (← inferType proof) (← goal.getType) do
          throwError "sin-ten interval: emitted proof has the wrong target"
        goal.assign (← instantiateMVars proof)
        replaceMainGoal []
  | _ => throwUnsupportedSyntax

private theorem endpointFact : Contains negativeFact (Real.sin 10) := by
  interval_sin_ten

/-- The generic chronology and proof frontend establish an endpoint-valued
interval enclosure for the original expression node. -/
theorem sinTenInterval : (-1 : ℝ) ≤ Real.sin 10 ∧ Real.sin 10 < 0 := by
  simpa [Contains, negativeFact, rat, ratValue] using endpointFact

/--
info: 'Hex.IntervalMathlib.SinTenIntervalConformance.sinTenInterval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sinTenInterval

end Hex.IntervalMathlib.SinTenIntervalConformance
