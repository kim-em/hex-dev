/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntExpNegative
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ negative exponential table

This fixture covers all 79 direct upper-bound declarations in the Table-10
`exp (-x)` block of PNT+ `IEANTN/LogTables.lean` at commit
`21998bb6196b56789f72a52656a781a75e134eb0`.  Every row is authenticated and
run through the same bounded sixth-power provider; the tight representative
`70/3` row also crosses generic chronology and `ProofFrontend` replay.
-/

namespace Hex.IntervalMathlib.PntExpNegativeConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntExpNegative

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? (value : Certificate) : Option (TargetRun.Result Bound Unit) := do
  let input := checkerInput value
  let .ok session := PolicySession.Session.start factDomain input.baseProgram
      packages input.initialFacts limits | none
  some (TargetRun.drive factDomain input.target.node input.target.fact firstOffer
    limits.policy.maxDecisions session ())

#guard certificates.length == 79
#guard certificates.all Certificate.valid
#guard certificates.all fun value => decode? (encode value) == some value
#guard certificates.all fun value => factFormat.validateBody (encode value)
#guard certificates.all fun value =>
  (run? value).any fun result =>
    match result.stop with
    | .target reached =>
        reached.fact == .upper value.upper && result.events.size == 1 &&
          result.session.state.engine.chronology == #[.fact 0]
    | _ => false

private def unknown : Certificate :=
  { representative with sourceIndex := 79 }

#guard
  (run? unknown).any fun result =>
    match result.stop with
    | .saturated => result.events.size == 1 &&
        result.session.state.engine.chronology.isEmpty &&
        result.session.arena.entries.isEmpty
    | _ => false

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name
  reached : TargetRun.Reached Bound

def fixture? : Option Fixture := do
  let result ← run? representative
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some { session := result.session, registry, reached }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .upper representative.upper &&
      fixture.registry.emit.find? factSchema.key == some ``factSchema

def trace? : Option (Frontend.Trace Bound) :=
  match fixture? with
  | none => none
  | some fixture => Frontend.trace? fixture.session.state.engine fixture.session.arena

#guard
  trace?.any fun trace =>
    trace.program == program &&
      match trace.events with
      | [.rule step] =>
          step.entry.replayKey == factSchema.key &&
            step.entry.body == encode representative &&
            step.assumptions == [{ node := node 0, fact := .exact representative.source }] &&
            step.event.node == node 1 &&
            step.event.fact == .upper representative.upper && step.previous == .all
      | _ => false

/-! ## Mutation rejection -/

private def action : Action :=
  { serial := 0, programVersion := 0, application := { index := 0 },
    rule := { index := 0 }, key := ruleKey, node := node 1, kind := .forward,
    effort := 0, generation := 0, inputs := [], writes := [node 1] }

private def replayContext : RuleFactContext representativeInput action :=
  { program, basePrefix := ProgramPrefix.refl program,
    assumptions := [{ node := node 0, fact := .exact representative.source }],
    proposed := { node := node 1, fact := .upper representative.upper } }

private def insufficientTerms : Certificate := { representative with terms := 13 }
private def wrongSixths : Certificate := { representative with sixths := 141 }
private def falseEndpoint : Certificate := { representative with numerator := 0 }
private def crossRow : Certificate :=
  (certificateFor? 38).getD defaultCertificate

#guard (decode? (encode insufficientTerms)).isNone
#guard (decode? (encode wrongSixths)).isNone
#guard (decode? (encode falseEndpoint)).isNone
#guard (factSchema.replay representativeInput action replayContext representative).isSome
#guard (factSchema.replay representativeInput action replayContext crossRow).isNone
#guard (factSchema.replay representativeInput action replayContext falseEndpoint).isNone

private def wrongSource : RuleFactContext representativeInput action :=
  { replayContext with assumptions := [{ node := node 0, fact := .exact crossRow.source }] }
private def wrongUpper : RuleFactContext representativeInput action :=
  { replayContext with proposed := { node := node 1, fact := .upper crossRow.upper } }

#guard (factSchema.replay representativeInput action wrongSource representative).isNone
#guard (factSchema.replay representativeInput action wrongUpper representative).isNone

theorem rejectFalseEndpoint : ¬ Real.exp (-(70 / 3 : ℝ)) < 0 := by
  exact not_lt_of_ge (Real.exp_pos _).le

/--
info: 'Hex.Interval.Experiment.PntExpNegative.exp_neg_10_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntExpNegative.exp_neg_10_lt

/--
info: 'Hex.Interval.Experiment.PntExpNegative.exp_neg_200_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PntExpNegative.exp_neg_200_lt

/-! ## Generic proof emission and ordinary theorem closure -/

def baseFacts : List (NodeFact Bound) :=
  [{ node := node 0, fact := .exact representative.source },
   { node := node 1, fact := .all }]

theorem baseWithin : FactsWithin program baseFacts := by
  intro fact member
  simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [program, node]

theorem basePrefix : ProgramPrefix program program := ProgramPrefix.refl program
theorem sameOperations : program.operations = program.operations := rfl

def initialExtension : Evidence (semantics.Extends program program) :=
  extendRefl semantics program

noncomputable def valuation : NodeId → ℝ
  | ⟨0⟩ => -(70 / 3)
  | ⟨1⟩ => Real.exp (-(70 / 3))
  | _ => 0

theorem valuationModels : semantics.models program valuation := by
  refine ⟨?_, ?_⟩
  · simp [program, operations, operationModels, sourceModel, expModel]
  rintro ⟨index⟩ instruction found
  cases index with
  | zero =>
      simp [Program.node?, program, sourceInstruction] at found
      subst instruction
      exact ⟨sourceModel, by rfl, by rfl⟩
  | succ index =>
      cases index with
      | zero =>
          simp [Program.node?, program, expInstruction] at found
          subst instruction
          exact ⟨expModel, by rfl, by rfl⟩
      | succ index => simp [Program.node?, program] at found

theorem closeRepresentative
    (result : Evidence
      (semantics.Entails program baseFacts representativeInput.target)) :
    Real.exp (-(70 / 3 : ℝ)) < 7.354e-11 := by
  have closed := result.proof valuation valuationModels (by
    intro fact member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change Contains (.exact representative.source) (valuation (node 0))
      norm_num [Contains, representative, certificateFor?, sourceRecord?,
        defaultCertificate, Certificate.source, valuation, node]
    · trivial)
  change Contains (.upper representative.upper) (valuation (node 1)) at closed
  norm_num [Contains, representative, certificateFor?, sourceRecord?,
    defaultCertificate, Certificate.upper, valuation, node] at closed ⊢
  exact closed

private def sourceExpr (value : Source) : Expr :=
  mkApp2 (mkConst ``Source.mk) (mkNatLit value.sourceIndex) (mkNatLit value.sixths)
private def upperExpr (value : Upper) : Expr :=
  mkApp3 (mkConst ``Upper.mk) (mkNatLit value.sourceIndex)
    (mkNatLit value.numerator) (mkNatLit value.scale)
private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .exact value => mkApp (mkConst ``Bound.exact) (sourceExpr value)
  | .upper value => mkApp (mkConst ``Bound.upper) (upperExpr value)
  | .empty => mkConst ``Bound.empty

private def boundEncoder : FrontendEncoder.Encoder Bound :=
  FrontendEncoder.make (mkConst ``Bound) (fun fact => pure (boundExpr fact))

private def seedAssumed (graph : Program) (base : List (NodeFact Bound))
    (index : Nat) (fact : NodeFact Bound) (found : base[index]? = some fact) :
    Evidence (semantics.Entails graph base fact) :=
  ProofEmitter.assumedAt graph base index fact found

private def frontendContext : ProofFrontend.Context Bound Name :=
  { encoder := boundEncoder, resolveSchema := pure,
    semantics := mkConst ``semantics, domain := mkConst ``boundSchema,
    laws := mkConst ``laws, stableLaw := mkConst ``stableLaw,
    input := mkConst ``representativeInput, assumed := ``seedAssumed,
    baseFacts, baseFactsTerm := mkConst ``baseFacts,
    baseProgram := program, baseProgramTerm := mkConst ``program,
    basePrefix := mkConst ``basePrefix, baseWithin := mkConst ``baseWithin,
    initialExtension := mkConst ``initialExtension,
    finalPrefix := mkConst ``basePrefix, sameOperations := mkConst ``sameOperations,
    top := boundSchema.top }

private meta def emitEvidence : MetaM Expr := do
  let some fixture := fixture?
    | throwError "pnt_exp_negative: search or registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_exp_negative: chronology quotation failed"
  let [.rule step] := trace.events
    | throwError "pnt_exp_negative: expected one rule event"
  unless step.entry.replayKey == factSchema.key &&
      step.entry.body == encode representative &&
      step.assumptions == [{ node := node 0, fact := .exact representative.source }] do
    throwError "pnt_exp_negative: emitted row drifted"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact representativeInput.target

/-- Ordinary-kernel representative emitted through generic checked replay. -/
theorem pntExpNeg70Thirds :
    Real.exp (-(70 / 3 : ℝ)) < 7.354e-11 := by
  run_tac
    let evidence ← emitEvidence
    let proof ← mkAppM ``closeRepresentative #[evidence]
    let goal ← getMainGoal
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "pnt_exp_negative: closed replay has the wrong theorem"
    goal.assign (← instantiateMVars proof)
    replaceMainGoal []

/--
info: 'Hex.IntervalMathlib.PntExpNegativeConformance.pntExpNeg70Thirds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pntExpNeg70Thirds

end Hex.IntervalMathlib.PntExpNegativeConformance
