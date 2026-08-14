/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Experiment.PntExpTail
import HexInterval.Experiment.ProofFrontend
import HexInterval.Experiment.TargetRun
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Source-pinned PNT+ exponential-tail acceptance probe

This fixture covers the numerical leaf inside
`LogTables.exp_neg_lt_1e_neg_100` at PNT+ commit
`21998bb6196b56789f72a52656a781a75e134eb0`.  Search consumes the bound
`y ≤ -231`, emits the package-owned range-reduction certificate, and generic
`ProofFrontend` replay closes the original reusable theorem for every
`x ≥ 231`.
-/

namespace Hex.IntervalMathlib.PntExpTailConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend ProofRegistry PntExpTail

private def firstOffer : TargetRun.Controller Bound Unit :=
  { update := fun state _ => state
    choose := fun state view =>
      match view.offers[0]? with
      | some offer => .select offer state
      | none => .stop state }

private def run? (input : CheckerInput Bound) :
    Option (TargetRun.Result Bound Unit) := do
  let .ok session := PolicySession.Session.start factDomain input.baseProgram
      packages input.initialFacts limits
    | none
  some (TargetRun.drive factDomain input.target.node input.target.fact
    firstOffer limits.policy.maxDecisions session ())

structure Fixture where
  session : PolicySession.Session Bound
  registry : ProofRegistry.Registry semantics Lean.Name
  reached : TargetRun.Reached Bound
  events : Array (TargetRun.Event Bound)

def fixture? : Option Fixture := do
  let result ← run? checkerInput
  let .target reached := result.stop | none
  let .ok registry := ProofRegistry.build result.session.registry proofPackages
    | none
  some
    { session := result.session
      registry
      reached
      events := result.events }

#guard
  fixture?.any fun fixture =>
    fixture.reached.seen == ({ node := node 1, version := 1 } : SeenVersion) &&
      fixture.reached.fact == .belowTenNeg100 && fixture.events.size == 1 &&
      fixture.session.state.engine.facts == #[.atMostNeg231, .belowTenNeg100] &&
      fixture.session.state.engine.chronology == #[.fact 0] &&
      fixture.registry.emit.find? tailFactSchema.key == some ``tailFactSchema

#guard
  baseFacts ==
      [{ node := node 0, fact := .atMostNeg231 },
        { node := node 1, fact := .all }] &&
    checkerInput.initialFacts == #[.atMostNeg231, .all]

/-! ## Node-position independence -/

private def offsetInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }

private def offsetProgram : Program :=
  { operations
    nodes := #[sourceInstruction, sourceInstruction, offsetInstruction] }

private def offsetInput : CheckerInput Bound :=
  { baseProgram := offsetProgram
    initialFacts := #[.atMostNeg231, .all, .all]
    target := { node := node 2, fact := .belowTenNeg100 } }

-- Planning follows the operation and watched input rather than a hardcoded
-- result-node position.
#guard
  (run? offsetInput).any fun result =>
    match result.stop with
    | .target reached =>
        reached.seen == ({ node := node 2, version := 1 } : SeenVersion) &&
          reached.fact == .belowTenNeg100 && result.events.size == 1 &&
          result.session.state.engine.facts ==
            #[.atMostNeg231, .all, .belowTenNeg100]
    | _ => false

private def offsetAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := tailRuleKey
    node := node 2
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node 2] }

private def offsetContext : RuleFactContext offsetInput offsetAction :=
  { program := offsetProgram
    basePrefix := ProgramPrefix.refl offsetProgram
    assumptions := [{ node := node 0, fact := .atMostNeg231 }]
    proposed := { node := node 2, fact := .belowTenNeg100 } }

#guard
  (tailFactSchema.replay offsetInput offsetAction offsetContext
    tailCertificate).isSome

/-! ## Boundary mutation rejection -/

private def input230 : CheckerInput Bound :=
  { checkerInput with initialFacts := #[.atMostNeg230, .all] }

-- `-230` is not a lower-precision form of the certified input.  Search
-- saturates without a proposal and without installing any payload.
#guard
  (run? input230).any fun result =>
    match result.stop with
    | .saturated =>
        result.events.size == 1 &&
          result.session.state.engine.facts == #[.atMostNeg230, .all] &&
          result.session.state.engine.chronology.isEmpty &&
          result.session.arena.entries.isEmpty
    | _ => false

#guard decodeCertificate? tailBody == some tailCertificate
#guard (decodeCertificate? [230, 100, 46, 125]).isNone
#guard (decodeCertificate? [231, 99, 46, 125]).isNone
#guard (decodeCertificate? [231, 100, 47, 125]).isNone
#guard factFormat.validateBody tailBody
#guard !factFormat.validateBody [230, 100, 46, 125]

private def action : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := tailRuleKey
    node := node 1
    kind := .forward
    effort := 0
    generation := 0
    inputs := []
    writes := [node 1] }

private def replayContext : RuleFactContext checkerInput action :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := [{ node := node 0, fact := .atMostNeg231 }]
    proposed := { node := node 1, fact := .belowTenNeg100 } }

#guard
  (tailFactSchema.replay checkerInput action replayContext tailCertificate).isSome

private def wrongInput : RuleFactContext checkerInput action :=
  { replayContext with
    assumptions := [{ node := node 0, fact := .atMostNeg230 }] }

private def wrongOutput : RuleFactContext checkerInput action :=
  { replayContext with proposed := { node := node 0, fact := .belowTenNeg100 } }

private def wrongFact : RuleFactContext checkerInput action :=
  { replayContext with proposed := { node := node 1, fact := .all } }

private def certificate230 : ReductionCertificate :=
  { tailCertificate with reductionPoint := 230 }

#guard (tailFactSchema.replay checkerInput action wrongInput tailCertificate).isNone
#guard (tailFactSchema.replay checkerInput action wrongOutput tailCertificate).isNone
#guard (tailFactSchema.replay checkerInput action wrongFact tailCertificate).isNone
#guard (tailFactSchema.replay checkerInput action replayContext certificate230).isNone

/-! ## Generic chronology and proof closure -/

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
          step.entry.replayKey == tailFactSchema.key &&
            step.event.programVersion == 0 && step.event.node == node 1 &&
            step.event.previous == ({ node := node 1, version := 0 } : SeenVersion) &&
            step.event.fact == .belowTenNeg100 && step.event.version == 1 &&
            step.assumptions == [{ node := node 0, fact := .atMostNeg231 }] &&
            step.previous == .all && step.entry.body == tailBody
      | _ => false

private def boundExpr : Bound → Expr
  | .all => mkConst ``Bound.all
  | .atMostNeg231 => mkConst ``Bound.atMostNeg231
  | .atMostNeg230 => mkConst ``Bound.atMostNeg230
  | .belowTenNeg100 => mkConst ``Bound.belowTenNeg100
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
    | throwError "pnt_exp_tail: search or proof registry failed"
  let some trace := Frontend.trace? fixture.session.state.engine fixture.session.arena
    | throwError "pnt_exp_tail: chronology quotation failed"
  unless trace.program == program do
    throwError "pnt_exp_tail: trace changed the expression graph"
  let [.rule step] := trace.events
    | throwError "pnt_exp_tail: expected exactly one rule event"
  unless step.entry.replayKey == tailFactSchema.key &&
      step.assumptions == [{ node := node 0, fact := .atMostNeg231 }] &&
      step.event.node == node 1 && step.event.fact == .belowTenNeg100 &&
      step.entry.body == tailBody do
    throwError "pnt_exp_tail: emitted event drifted from the pinned provider"
  let state ← ProofFrontend.emitTrace frontendContext trace.program trace.events
    fixture.registry.emit
  ProofFrontend.closeTarget frontendContext state fixture.reached.seen
    fixture.reached.fact checkerInput.target

/-- Generic frontend evidence for the package-owned tail certificate. -/
private noncomputable def replayEvidence : Evidence
    (semantics.Entails program baseFacts checkerInput.target) := by
  run_tac
    let evidence ← emitEvidence
    let goal ← getMainGoal
    unless ← isDefEq (← inferType evidence) (← goal.getType) do
      throwError "pnt_exp_tail: replay evidence has the wrong theorem"
    goal.assign (← instantiateMVars evidence)
    replaceMainGoal []

/-- Source-pinned reusable PNT+ statement, with the boundary certificate
replayed once and monotonicity supplied at theorem closure. -/
theorem pntExpTail {x : ℝ} (hx : 231 ≤ x) : Real.exp (-x) < 1e-100 :=
  closeTail x hx replayEvidence

/-- The numerical leaf used by the pinned source declaration. -/
theorem pntExpBoundary : Real.exp (-(231 : ℝ)) < 1e-100 :=
  pntExpTail (x := 231) (by norm_num)

/--
info: 'Hex.IntervalMathlib.PntExpTailConformance.pntExpTail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntExpTail

/--
info: 'Hex.IntervalMathlib.PntExpTailConformance.pntExpBoundary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pntExpBoundary

/--
info: 'Hex.Interval.Experiment.PntExpTail.reject230' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reject230

end Hex.IntervalMathlib.PntExpTailConformance
