/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntBKLNWPow
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Checked PNT+ BKLNW power-fold acceptance

The Mathlib-free package authenticates the split coordinates, base table,
exact tail cardinality, and source rational endpoint.  The original `pow433`
two-band canary and the parameterized fine ladder together cover all eleven
source `pow*_upper` declarations without importing LeanCert.
-/

namespace Hex.IntervalMathlib.PntBKLNWPowConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntBKLNWPow

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? : Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain program packages
      checkerInput.initialFacts limits
    | none
  some (TargetRun.drive factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name
  reached : TargetRun.Reached Bound

def fixture? : Option Fixture := do
  let result ← run?
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { session := result.session, registry, reached }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .upper &&
      fixture.session.state.engine.facts == #[.upper] &&
      fixture.session.state.engine.chronology == #[.fact 0] &&
      fixture.registry.emit.find? foldFactSchema.key == some ``foldFactSchema

#guard baseFacts == [{ node, fact := .all }]
#guard checkerInput.initialFacts == #[.all]

/-! ## Load-bearing certificate mutations -/

private def wrongLimitBody : List Nat :=
  [432, 4, 5, 36, 57, 429, 100000001948, 100000000000]

private def wrongCardinalityBody : List Nat :=
  [433, 4, 5, 36, 57, 428, 100000001948, 100000000000]

private def unsupportedExponentBody : List Nat :=
  [433, 4, 5, 37, 57, 429, 100000001948, 100000000000]

private def unsupportedTailExponentBody : List Nat :=
  [433, 4, 5, 36, 58, 429, 100000001948, 100000000000]

private def wrongEndpointBody : List Nat :=
  [433, 4, 5, 36, 57, 429, 100000001900, 100000000000]

#guard decodeCertificate? body == some certificate
#guard (decodeCertificate? wrongLimitBody).isSome
#guard (decodeCertificate? wrongCardinalityBody).isSome
#guard (decodeCertificate? unsupportedExponentBody).isSome
#guard (decodeCertificate? unsupportedTailExponentBody).isSome
#guard (decodeCertificate? wrongEndpointBody).isSome
#guard factFormat.validateBody body
#guard !factFormat.validateBody wrongLimitBody
#guard !factFormat.validateBody wrongCardinalityBody
#guard !factFormat.validateBody unsupportedExponentBody
#guard !factFormat.validateBody unsupportedTailExponentBody
#guard !factFormat.validateBody wrongEndpointBody

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

private def planFails (cells : List Nat) : Bool :=
  match (planForBody cells request).outcome with
  | .failed _ => (planForBody cells request).drafts.isEmpty
  | _ => false

#guard planFails wrongLimitBody
#guard planFails wrongCardinalityBody
#guard planFails unsupportedExponentBody
#guard planFails unsupportedTailExponentBody
#guard planFails wrongEndpointBody

private def replayContext : RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := []
    proposed := { node, fact := .upper } }

#guard
  (foldFactSchema.replay checkerInput action replayContext certificate).isSome

private def wrongLimit : FoldCertificate := { certificate with limit := 432 }
private def wrongCardinality : FoldCertificate :=
  { certificate with tailCardinality := 428 }
private def unsupportedExponent : FoldCertificate :=
  { certificate with isolatedExponent := 37 }
private def unsupportedTailExponent : FoldCertificate :=
  { certificate with tailExponent := 58 }
private def wrongEndpoint : FoldCertificate :=
  { certificate with targetNumerator := 100000001900 }

private def wrongFact : RuleFactContext checkerInput action :=
  { replayContext with proposed := { node, fact := .all } }

#guard (foldFactSchema.replay checkerInput action replayContext wrongLimit).isNone
#guard (foldFactSchema.replay checkerInput action replayContext wrongCardinality).isNone
#guard (foldFactSchema.replay checkerInput action replayContext unsupportedExponent).isNone
#guard (foldFactSchema.replay checkerInput action replayContext unsupportedTailExponent).isNone
#guard (foldFactSchema.replay checkerInput action replayContext wrongEndpoint).isNone
#guard (foldFactSchema.replay checkerInput action wrongFact certificate).isNone

/-! ## Complete parameterized ladder schema -/

private def smallerLadder : List LadderCertificate :=
  [ladder29, ladder37, ladder44, ladder51, ladder58,
    ladder63, ladder145, ladder217, ladder289, ladder361]

private def ladderPlanSucceeds (value : LadderCertificate) : Bool :=
  let plan := ladderPlanForBody (ladderCertificateBody value) request
  match plan.outcome with
  | .success _ _ _ => !plan.drafts.isEmpty
  | _ => false

private def ladderPlanFails (value : LadderCertificate) : Bool :=
  let plan := ladderPlanForBody (ladderCertificateBody value) request
  match plan.outcome with
  | .failed _ => plan.drafts.isEmpty
  | _ => false

private def runLadder? (value : LadderCertificate) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := ladderStart value | none
  some (TargetRun.drive factDomain checkerInput.target.node checkerInput.target.fact
    firstOffer limits.policy.maxDecisions session ())

#guard smallerLadder.all validLadderCertificate
#guard smallerLadder.all fun value =>
  decodeLadderCertificate? (ladderCertificateBody value) == some value
#guard smallerLadder.all fun value => ladderFactFormat.validateBody
  (ladderCertificateBody value)
#guard smallerLadder.all ladderPlanSucceeds
#guard smallerLadder.all fun value =>
  (runLadder? value).any fun result =>
    match result.stop with
    | .target reached => reached.fact == .upper
    | _ => false

private def wrongLadderLimit : LadderCertificate :=
  { ladder29 with limit := 30 }
private def wrongLadderSplit : LadderCertificate :=
  { ladder29 with exactStop := 19 }
private def wrongLadderTail : LadderCertificate :=
  { ladder29 with tailCardinality := 8 }
private def wrongLadderScale : LadderCertificate :=
  { ladder29 with baseDenominator := 10000000 }
private def wrongLadderEndpoint : LadderCertificate :=
  { ladder29 with targetNumerator := 10000, targetDenominator := 10000 }

private def ladderMutations : List LadderCertificate :=
  [wrongLadderLimit, wrongLadderSplit, wrongLadderTail,
    wrongLadderScale, wrongLadderEndpoint]

/- Every mutation remains syntactically decodable; rejection is semantic. -/
#guard ladderMutations.all fun value =>
  (decodeLadderCertificate? (ladderCertificateBody value)).isSome
#guard ladderMutations.all fun value =>
  !ladderFactFormat.validateBody (ladderCertificateBody value)
#guard ladderMutations.all ladderPlanFails

#guard smallerLadder.all fun value =>
  ((ladderFoldFactSchema value).replay checkerInput action replayContext value).isSome

/- A valid certificate for another source row cannot replay against the
selected operation model. -/
#guard
  ((ladderFoldFactSchema ladder29).replay checkerInput action replayContext
    ladder37).isNone
#guard
  ((ladderFoldFactSchema ladder29).replay checkerInput action replayContext
    wrongLadderEndpoint).isNone

/-! ## Generic chronology and ordinary theorem closure -/

def trace? : Option (Frontend.Trace Bound) := do
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program &&
      match trace.events with
      | [.rule step] =>
          step.entry.replayKey == foldFactSchema.key &&
            step.event.node == node && step.event.fact == .upper &&
            step.assumptions == [] && step.previous == .all &&
            step.entry.body == body
      | _ => false

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .upper => mkConst ``Bound.upper
  | .empty => mkConst ``Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))

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
    | throwError "pnt_bklnw_pow: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_bklnw_pow: chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "pnt_bklnw_pow: expected exactly one rule event"
  unless trace.program == program &&
      step.entry.replayKey == foldFactSchema.key &&
      step.event.node == node && step.event.fact == .upper &&
      step.assumptions == [] && step.entry.body == body do
    throwError "pnt_bklnw_pow: emitted event drifted from the checked certificate"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target

private noncomputable def replayEvidence : Evidence
    (semantics.Entails program baseFacts checkerInput.target) := by
  run_tac
    let evidence ← emitEvidence
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_bklnw_pow: replay evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

/-- Source-pinned replacement for PNT+ `cert_pow433_upper`, obtained through
generic package planning, chronological replay, and the proof frontend. -/
theorem pntPow433 :
    (1 + 193571378 / (10 : ℝ) ^ 16) * sourceF ((2 : ℝ) ^ (433 : Nat)) ≤
      (1.00000001937 : ℝ) + (1 : ℝ) / 10 ^ 8 :=
  closePow replayEvidence

/--
info: 'Hex.IntervalMathlib.PntBKLNWPowConformance.pntPow433' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntPow433

/--
info: 'Hex.Interval.Experiment.PntBKLNWPow.rejectWrongEndpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rejectWrongEndpoint

/--
info: 'Hex.Interval.Experiment.PntBKLNWPow.certPow29Upper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms certPow29Upper

/--
info: 'Hex.Interval.Experiment.PntBKLNWPow.certPow361Upper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms certPow361Upper

/--
info: 'Hex.Interval.Experiment.PntBKLNWPow.ladderCertificateUpper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ladderCertificateUpper

/--
info: 'Hex.Interval.Experiment.PntBKLNWPow.rejectPow29Endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rejectPow29Endpoint

end Hex.IntervalMathlib.PntBKLNWPowConformance
