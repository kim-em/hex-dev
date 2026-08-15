/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntBKLNWExp
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Checked PNT+ BKLNW exponential-fold acceptance

One source-indexed certificate schema covers all 22 lower/upper declarations
at the eleven pinned exponential arguments. The runtime authenticates the
floor, exact/table-tail split, rational scale, and both output cuts.
-/

namespace Hex.IntervalMathlib.PntBKLNWExpConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntBKLNWExp

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? (value : Certificate) : Option (TargetRun.Result Bound Unit) := do
  let .ok session := start value | none
  some (TargetRun.drive factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer (limitsFor value).policy.maxDecisions session ())

#guard certificates.length == 11
#guard certificates.all validCertificate
#guard arithmeticWork exp20 == 1000
#guard arithmeticWork exp300 == 36300
#guard certificates.all fun value =>
  decodeCertificate? (certificateBody value) == some value
#guard certificates.all fun value => factFormat.validateBody (certificateBody value)
#guard certificates.all fun value =>
  (run? value).any fun result =>
    match result.stop with
    | .target reached => reached.fact == .window
    | _ => false

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := foldRuleKey
    node
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node] }

private def programView : ProgramView :=
  { programVersion := 0
    operations := program.operations
    nodes := program.nodes
    generations := #[0]
    depths := #[0] }

private def request : RuleRequest Bound :=
  { action
    program := programView
    inputs := []
    writes := [node] }

private def planFails (value : Certificate) : Bool :=
  match (planForBody (certificateBody value) request).outcome with
  | .failed _ => (planForBody (certificateBody value) request).drafts.isEmpty
  | _ => false

private def wrongSource : Certificate := { exp20 with sourceIndex := 1 }
private def wrongArgument : Certificate := { exp20 with argument := 21 }
private def wrongFloor : Certificate := { exp20 with floor := 29 }
private def wrongSplit : Certificate := { exp100 with exactStop := 62 }
private def wrongTailStart : Certificate := { exp100 with tailStart := 63 }
private def wrongTail : Certificate := { exp100 with tailCardinality := 80 }
private def wrongScale : Certificate := { exp20 with baseDenominator := 10 ^ 11 }
private def wrongLower : Certificate := { exp20 with lowerNumerator := 20000 }
private def wrongUpper : Certificate := { exp20 with upperNumerator := 10000 }

private def mutations : List Certificate :=
  [wrongSource, wrongArgument, wrongFloor, wrongSplit, wrongTailStart, wrongTail,
    wrongScale, wrongLower, wrongUpper]

/- Every mutation remains syntactically decodable; rejection is semantic. -/
#guard mutations.all fun value =>
  (decodeCertificate? (certificateBody value)).isSome
#guard mutations.all fun value => !factFormat.validateBody (certificateBody value)
#guard mutations.all planFails

private def replayContext : RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node, fact := .window } }

#guard certificates.all fun value =>
  ((foldFactSchema value).replay checkerInput action replayContext value).isSome

/- Valid rows are not interchangeable even though they share a schema. -/
#guard
  ((foldFactSchema exp20).replay checkerInput action replayContext exp25).isNone
#guard
  ((foldFactSchema exp100).replay checkerInput action replayContext exp150).isNone
#guard
  ((foldFactSchema exp20).replay checkerInput action replayContext wrongLower).isNone

private def wrongFact : RuleFactContext checkerInput action :=
  { replayContext with proposed := { node, fact := .all } }

#guard ((foldFactSchema exp20).replay checkerInput action wrongFact exp20).isNone

/- The endpoint mutations are mathematically false, not merely unrecognized. -/
theorem rejectLowerEndpoint :
    ¬ (2 : ℝ) ≤ (1 + 193571378 / (10 : ℝ) ^ 16) *
      PntBKLNWPow.sourceF (Real.exp 20) := by
  intro lower
  have upper := exp20Provider.2
  norm_num at upper
  linarith

theorem rejectUpperEndpoint :
    ¬ (1 + 193571378 / (10 : ℝ) ^ 16) *
        PntBKLNWPow.sourceF (Real.exp 20) ≤ (1 : ℝ) := by
  intro upper
  have lower := exp20Provider.1
  norm_num at lower
  linarith

/-! ## Generic chronology and ordinary theorem closure -/

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry (semantics exp20) Lean.Name
  reached : TargetRun.Reached Bound

def fixture? : Option Fixture := do
  let result ← run? exp20
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry
      exp20ProofPackages | none
  some { session := result.session, registry, reached }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .window &&
      fixture.session.state.engine.facts == #[.window] &&
      fixture.session.state.engine.chronology == #[.fact 0] &&
      fixture.registry.emit.find? exp20FactSchema.key ==
        some ``exp20FactSchema

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program &&
      match trace.events with
      | [.rule step] =>
          step.entry.replayKey == exp20FactSchema.key &&
            step.event.node == node && step.event.fact == .window &&
            step.assumptions == [] && step.previous == .all &&
            step.entry.body == certificateBody exp20
      | _ => false

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .window => mkConst ``Bound.window
  | .empty => mkConst ``Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))

private def seedAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence ((semantics exp20).Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def frontendContext : ProofFrontend.Context Bound Name :=
  { encoder := boundEncoder
    resolveSchema := pure
    semantics := mkApp (mkConst ``semantics) (mkConst ``exp20)
    domain := mkApp (mkConst ``boundSchema) (mkConst ``exp20)
    laws := mkApp (mkConst ``laws) (mkConst ``exp20)
    stableLaw := mkApp (mkConst ``stableLaw) (mkConst ``exp20)
    input := mkConst ``checkerInput
    assumed := ``seedAssumed
    baseFacts
    baseFactsTerm := mkConst ``baseFacts
    baseProgram := program
    baseProgramTerm := mkConst ``program
    basePrefix := mkConst ``basePrefix
    baseWithin := mkConst ``baseWithin
    initialExtension := mkApp (mkConst ``initialExtension) (mkConst ``exp20)
    finalPrefix := mkConst ``basePrefix
    sameOperations := mkConst ``sameOperations
    top := (boundSchema exp20).top }

private meta def emitEvidence : MetaM Expr := do
  let some fixture := fixture?
    | throwError "pnt_bklnw_exp: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_bklnw_exp: chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "pnt_bklnw_exp: expected exactly one rule event"
  unless trace.program == program &&
      step.entry.replayKey == exp20FactSchema.key &&
      step.event.node == node && step.event.fact == .window &&
      step.assumptions == [] && step.entry.body == certificateBody exp20 do
    throwError "pnt_bklnw_exp: emitted event drifted from the checked certificate"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target

private noncomputable def replayEvidence : Evidence
    ((semantics exp20).Entails program baseFacts checkerInput.target) := by
  run_tac
    let evidence ← emitEvidence
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_bklnw_exp: replay evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

/-- The source `b = 20` window closed through generic package planning,
chronological replay, and `ProofFrontend`; the same checked schema accepts all
eleven source records. -/
theorem pntExp20 :
    (14262 : ℝ) / 10000 ≤
        (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 20) ∧
      (1 + 193571378 / (10 : ℝ) ^ 16) *
          PntBKLNWPow.sourceF (Real.exp 20) ≤ (14263 : ℝ) / 10000 :=
  closeWindow exp20 replayEvidence

/--
info: 'Hex.IntervalMathlib.PntBKLNWExpConformance.pntExp20' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntExp20

/--
info: 'Hex.Interval.Experiment.PntBKLNWExp.certificateWindow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms certificateWindow

/--
info: 'Hex.Interval.Experiment.PntBKLNWExp.a2Exp300Upper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a2Exp300Upper

/--
info: 'Hex.IntervalMathlib.PntBKLNWExpConformance.rejectLowerEndpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rejectLowerEndpoint

end Hex.IntervalMathlib.PntBKLNWExpConformance
