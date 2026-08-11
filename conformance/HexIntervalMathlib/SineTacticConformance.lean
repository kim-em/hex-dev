/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.SineProofConformance
import HexInterval.Experiment.ProofFrontend
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Tactic-frontend canary for arbitrary-function interval search

`interval_sine` runs the opaque live planner at elaboration time, extracts its
proof-producing events, and reifies them as ordinary Lean terms.  It selects
package-owned schemas from the events' full replay addresses and constructs
the instance, two rule, equality-transport, and caller-closure applications in
dependency order.  The literal comparison below is a separate quotation
regression; the tactic's proof path consumes the actual returned data.

The compiled planner remains outside the trusted proof.  A planner or quoting
bug can make the tactic reject; it cannot create a theorem, because the term
assigned to the goal is checked by Lean's kernel.
-/

namespace Hex.IntervalMathlib.SineTacticConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PayloadArena SemanticReplay ChronologicalReplay ProofEmitter
open Frontend ProofFrontend
open SineSign SineSignConformance SineProofConformance

private structure LiveQuotes where
  instantiation : InstanceQuote
  sine : RuleStep Range
  negation : RuleStep Range
  transport : TransportStep Range

/-! ## A second-instantiation canary -/

private def noopKey : RuleKey :=
  { name := "sine-sign.noop-instance" }

private def noopAction : Action :=
  { serial := 4
    programVersion := 1
    application := { index := 5 }
    rule := { index := 3 }
    key := noopKey
    node := node 4
    kind := .instantiate
    effort := 0
    generation := 1
    inputs := []
    writes := [] }

private def noopEvent : InstanceEvent :=
  { programVersion := 2
    origin := noopAction
    family := 2
    substitution := [node 4]
    products := []
    newNodes := []
    generation := 2
    equalities := [{ index := 0 }]
    newEqualities := []
    payload := payload 9 }

private def noopEntry : Entry :=
  { origin := noopAction
    role := .instance
    schema := 1
    body := [] }

private def noopQuote : InstanceQuote :=
  { event := noopEvent
    payload := payload 9
    entry := noopEntry }

private def noopSchema : PackedInstanceSchema semantics where
  rule := noopKey
  schema := 1
  Certificate := Unit
  decode := fun body => if body.isEmpty then some () else none
  replay := fun _ _ context _ =>
    if same : context.before = context.after then
      some
        { proof := by
            simpa only [same] using
              (extendRefl semantics context.before).proof }
    else
      none

private def noopEmit : EmitPackage Name :=
  { schemas :=
      [{ key := noopSchema.key
         handle := ``noopSchema }] }

/-- Extract the complete proof-event list from the actual returned state. -/
private def liveTrace? : Option (Frontend.Trace Range) :=
  match transported? with
  | none => none
  | some session => do
      let engine := session.state.engine
      if !session.live || session.droppedWork || engine.equalities.size != 1 then
        none
      else
        pure ()
      Frontend.trace? engine session.arena

/-- Specialize the generic quote to the literal-regression fixture. -/
private def liveQuotes? : Option LiveQuotes := do
  let trace <- liveTrace?
  let [.instantiation instantiation, .rule sine, .rule negation,
      .transport transport] := trace.events | none
  pure { instantiation, sine, negation, transport }

#guard
  transported?.any fun session =>
    let engine := session.state.engine
    (Frontend.quote? engine session.arena
      engine.chronology.toList 0 0).isSome &&
      (Frontend.quote? engine session.arena
        [.instance 0, .fact 0, .fact 0, .fact 2] 0 0).isNone &&
      (Frontend.quote? engine session.arena
        [.instance 0, .fact 0, .fact 1] 0 0).isNone

private def rangeExpr : Range -> Expr
  | .all => mkConst ``Range.all
  | .unit => mkConst ``Range.unit
  | .nonnegative => mkConst ``Range.nonnegative
  | .nonpositive => mkConst ``Range.nonpositive
  | .zero => mkConst ``Range.zero
  | .empty => mkConst ``Range.empty

/-- The one structural encoder used by both quotation regression and proof
emission. -/
private def frontendEncoder : FrontendEncoder.Encoder Range :=
  FrontendEncoder.make (mkConst ``Range) (fun fact => pure (rangeExpr fact))

private meta def checkQuote (label : String) (actual expected : Expr) : MetaM Unit := do
  unless <- isDefEq actual expected do
    throwError "interval_sine: reified {label} does not match its checked proof step"

private meta def schemaName (table : SchemaTable Name) (label : String)
    (entry : Entry) : MetaM Name := do
  let some declaration := table.find? entry.replayKey
    | throwError "interval_sine: no proof schema for {label}"
  discard <| getConstInfo declaration
  pure declaration

private meta def checkSchema (table : SchemaTable Name) (label : String)
    (entry : Entry) (expected : Name) : MetaM Unit := do
  let declaration <- schemaName table label entry
  unless declaration == expected do
    throwError "interval_sine: wrong proof schema selected for {label}"

private meta def checkQuoteData (quote : LiveQuotes) : MetaM Unit := do
  let some table := emitTable?
    | throwError "interval_sine: duplicate proof-schema address"
  checkSchema table "instantiation" quote.instantiation.entry
    ``oddnessInstanceSchema
  checkSchema table "sine rule" quote.sine.entry ``sineFactSchema
  checkSchema table "negation rule" quote.negation.entry ``negationFactSchema
  checkSchema table "equality transport" quote.transport.entry
    ``oddnessEqualitySchema
  checkQuote "instantiation"
    (← frontendEncoder.instanceQuote quote.instantiation)
    (mkConst ``instanceQuote)
  checkQuote "sine rule" (← frontendEncoder.ruleStep quote.sine)
    (mkConst ``sineStep)
  checkQuote "negation rule" (← frontendEncoder.ruleStep quote.negation)
    (mkConst ``negationStep)
  checkQuote "equality transport"
    (← frontendEncoder.transportStep quote.transport)
    (mkConst ``transportStep)

/-- Specialize generic caller-assumption seeding to this semantics adapter;
the elaborator still supplies the program, base list, index, and fact. -/
private def seedAssumed (program : Program) (base : List (NodeFact Range))
    (index : Nat) (fact : NodeFact Range) (found : base[index]? = some fact) :
    Evidence (semantics.Entails program base fact) :=
  ProofEmitter.assumedAt program base index fact found

/-- The real-sine adapter for the function-independent proof-event fold. -/
private def frontendContext : ProofFrontend.Context Range Name :=
  { encoder := frontendEncoder
    resolveSchema := pure
    semantics := mkConst ``semantics
    domain := mkConst ``rangeSchema
    laws := mkConst ``laws
    stableLaw := mkConst ``stableLaw
    input := mkConst ``checkerInput
    assumed := ``seedAssumed
    baseFacts
    baseFactsTerm := mkConst ``baseFacts
    baseProgram := SineSign.baseProgram
    baseProgramTerm := mkConst ``baseProgram
    basePrefix := mkConst ``basePrefix
    baseWithin := mkConst ``baseWithin
    initialExtension := mkConst ``initialExtension
    finalPrefix := mkConst ``programPrefix
    sameOperations := mkConst ``sameOperations
    top := fun domain => rangeSchema.top domain }

/-- Emit a proof by folding arbitrary fact events through an exact
`(node, version)` evidence table and reconstructed program state.  The event
fold does not name any function or propagator; packages are selected only
through their replay addresses. -/
private meta def emitTrace (programValue : Program)
    (events : List (Frontend.Event Range))
    (table : SchemaTable Name) :
    MetaM Expr := do
  let state ←
    ProofFrontend.emitTrace frontendContext programValue events table
  let target := { node := node 2, version := 1 : SeenVersion }
  let some final := ProofFrontend.findProof? state.known target .nonpositive
    | throwError "interval_sine: trace did not prove the requested target"
  mkAppM ``closeEvidence #[state.extension, final]

private meta def emitQuote (quote : LiveQuotes) (table : SchemaTable Name) :
    MetaM Expr :=
  emitTrace extendedProgram
    [ .instantiation quote.instantiation, .rule quote.sine,
      .rule quote.negation, .transport quote.transport ] table

/-- Reify the planner's returned data, validate the quote, and emit its proof
chain.  Every replay success witness in the returned term is ordinary `rfl`. -/
private meta def emitLiveEvidence : MetaM Expr := do
  let some trace := liveTrace?
    | throwError "interval_sine: compiled interval search failed"
  let some table := emitTable?
    | throwError "interval_sine: duplicate proof-schema address"
  emitTrace trace.program trace.events table

/-- Reify the planner's returned data and bind it to the proof-side literals.
This comparison is a liveness/fidelity gate, not evidence for the theorem. -/
private meta def checkLiveQuote : MetaM Unit := do
  let some quote := liveQuotes?
    | throwError "interval_sine: compiled interval search failed"
  checkQuoteData quote

/-- Find two local hypotheses accepted by the emitted sine theorem and build
an application whose inferred target is definitionally the caller's goal. -/
private meta def proveSine (target : Expr) : MetaM Expr := do
  unless quotesMatchSearch do
    throwError "interval_sine: compiled interval search did not match the checked proof quote"
  checkLiveQuote
  let context <- getLCtx
  for first in context do
    unless first.isImplementationDetail do
      for second in context do
        unless second.isImplementationDetail do
          let saved <- saveState
          let probe? <- observing? <|
            mkAppM ``emittedSineTheorem
              #[mkFVar first.fvarId, mkFVar second.fvarId]
          match probe? with
          | some probe =>
            if <- isDefEq (← inferType probe) target then
              let evidence <- emitLiveEvidence
              let proof <- mkAppM ``closeSine
                #[evidence, mkFVar first.fvarId, mkFVar second.fvarId]
              unless <- isDefEq (← inferType proof) target do
                throwError "interval_sine: emitted replay has the wrong target"
              return (← instantiateMVars proof)
            saved.restore
          | none => saved.restore
  throwError
    "interval_sine: expected hypotheses matching `0 ≤ x` and `x ≤ 1` and goal `Real.sin (-x) ≤ 0`"

/-- Run the real-sine interval planner, quote its trace, and emit its proof. -/
syntax (name := intervalSineTac) "interval_sine" : tactic

@[tactic intervalSineTac] meta def evalIntervalSine : Tactic := fun stx => do
  match stx with
  | `(tactic| interval_sine) =>
      let goal <- getMainGoal
      goal.withContext do
        let target <- instantiateMVars (← goal.getType)
        let proof <- proveSine target
        goal.assign proof
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

/-- Named trust-surface regression for the planner-backed direct emitter. -/
theorem tacticSine {x : ℝ} (upper : x ≤ 1) (lower : 0 ≤ x) :
    Real.sin (-x) ≤ 0 := by
  interval_sine

example {x : ℝ} (_upper : x ≤ 1) (_lower : 0 ≤ x) : True := by
  fail_if_success interval_sine
  trivial

set_option linter.unusedTactic false in
example : True := by
  run_tac
    let some quote := liveQuotes?
      | throwError "interval_sine test: compiled search failed"
    let malformed : LiveQuotes :=
      { quote with sine := { quote.sine with payload := { index := 99 } } }
    checkQuoteData quote
    let some table := emitTable?
      | throwError "interval_sine test: duplicate proof-schema address"
    let some repeatTable :=
        SchemaTable.build [negationEmit, sineEmit, noopEmit]
      | throwError "interval_sine test: repeated-instance schema table failed"
    let lateTransport : TransportStep Range :=
      { quote.transport with
        event := { quote.transport.event with programVersion := 2 } }
    let _ <- emitTrace extendedProgram
        [ .instantiation quote.instantiation, .rule quote.sine,
          .rule quote.negation, .instantiation noopQuote,
          .transport lateTransport ] repeatTable
    let oversizedNoop : InstanceQuote :=
      { noopQuote with
        event := { noopQuote.event with newNodes := [node 4] } }
    if (← observing? (emitTrace extendedProgram
        [ .instantiation quote.instantiation, .rule quote.sine,
          .rule quote.negation, .instantiation oversizedNoop,
          .transport lateTransport ] repeatTable)).isSome then
      throwError "interval_sine test: oversized repeated instantiation was accepted"
    let reordered : List (Frontend.Event Range) :=
      [ .instantiation quote.instantiation, .rule quote.negation,
        .rule quote.sine, .transport quote.transport ]
    if (← observing? (emitTrace extendedProgram reordered table)).isSome then
      throwError "interval_sine test: future fact was accepted as a dependency"
    let wrongVersion : TransportStep Range :=
      { quote.transport with
        event := { quote.transport.event with programVersion := 2 } }
    if (← observing? (emitTrace extendedProgram
        [ .instantiation quote.instantiation, .rule quote.sine,
          .rule quote.negation, .transport wrongVersion ] table)).isSome then
      throwError "interval_sine test: stale transport program version was accepted"
    let staleSine : RuleStep Range :=
      { quote.sine with
        event := { quote.sine.event with programVersion := 2 } }
    if (← observing? (emitTrace extendedProgram
        [ .instantiation quote.instantiation, .rule staleSine,
          .rule quote.negation, .transport quote.transport ] table)).isSome then
      throwError "interval_sine test: stale rule program version was accepted"
    if (← observing? (emitTrace baseProgram
        [ .instantiation quote.instantiation, .rule quote.sine,
          .rule quote.negation, .transport quote.transport ] table)).isSome then
      throwError "interval_sine test: absent generated nodes were accepted"
    if (← observing? (checkQuoteData malformed)).isSome then
      throwError "interval_sine test: malformed quote was accepted"
    if (← observing? (emitQuote malformed table)).isSome then
      throwError "interval_sine test: malformed proof emission was accepted"
    let some missingTable := SchemaTable.build [negationEmit]
      | throwError "interval_sine test: missing-schema fixture did not build"
    if (← observing? (emitQuote quote missingTable)).isSome then
      throwError "interval_sine test: missing proof schema was accepted"
    let some wrongTable := SchemaTable.build [negationEmit, wrongSineEmit]
      | throwError "interval_sine test: wrong-schema fixture did not build"
    if (← observing? (emitQuote quote wrongTable)).isSome then
      throwError "interval_sine test: wrong proof schema was accepted"
    let missing := { quote.sine.entry with schema := 99 }
    if (← observing?
        (checkSchema table "missing-schema test" missing ``sineFactSchema)).isSome then
      throwError "interval_sine test: missing schema was accepted"
    if (← observing?
        (checkSchema table "wrong-schema test" quote.negation.entry
          ``sineFactSchema)).isSome then
      throwError "interval_sine test: wrong schema was accepted"
  trivial

end Hex.IntervalMathlib.SineTacticConformance
