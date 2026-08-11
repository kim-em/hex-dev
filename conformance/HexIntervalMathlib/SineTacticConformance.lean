/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.SineProofConformance
import Mathlib.Lean.Elab.Tactic.Meta

/-!
# Tactic-frontend canary for arbitrary-function interval search

`interval_sine` runs the opaque live planner at elaboration time, extracts its
proof-producing events, and reifies them as ordinary Lean terms.  This first
frontend canary checks those terms against the transparent proof chain before
applying its end-user theorem.  It is deliberately narrow: schema selection
and assembly of an arbitrary reified trace are the next experiment.

The compiled planner remains outside the trusted proof.  A planner or quoting
bug can make the tactic reject; it cannot create a theorem, because the term
assigned to the goal is checked by Lean's kernel.
-/

namespace Hex.IntervalMathlib.SineTacticConformance

open Lean Elab Tactic Meta
open Hex.Interval.Experiment
open Propagator PayloadArena SemanticReplay ProofEmitter
open SineSign SineSignConformance SineProofConformance

private structure LiveQuotes where
  instantiation : InstanceQuote
  sine : RuleStep Range
  negation : RuleStep Range
  transport : TransportStep Range

private def resolveFacts? (engine : Engine Range) (inputs : List SeenVersion) :
    Option (List (NodeFact Range)) :=
  inputs.mapM fun input => do
    let fact <- engine.factAt? input
    pure { node := input.node, fact }

private def ruleStep? (engine : Engine Range) (arena : Arena)
    (event : FactEvent Range) : Option (RuleStep Range) := do
  let .rule action _ payload := event.cause | none
  let entry <- arena.entry? payload .fact
  let assumptions <- resolveFacts? engine action.inputs
  let previous <- engine.factAt? event.previous
  pure { event, payload, entry, assumptions, previous }

private def transportStep? (engine : Engine Range) (arena : Arena)
    (event : FactEvent Range) : Option (TransportStep Range) := do
  let .transport equality source := event.cause | none
  let edge <- engine.equalities[equality.index]?
  let entry <- arena.entry? edge.payload .equality
  let assumptions <- resolveFacts? engine edge.origin.inputs
  let previous <- engine.factAt? event.previous
  let sourceFact <- engine.factAt? source
  pure
    { event
      equality
      edge
      payload := edge.payload
      entry
      assumptions
      previous
      sourceFact }

/-- Extract the proof-side quote from the actual returned search state. -/
private def liveQuotes? : Option LiveQuotes :=
  match transported? with
  | none => none
  | some session => do
      let engine := session.state.engine
      if !session.live || session.droppedWork ||
          engine.instanceHistory.size != 1 || engine.equalities.size != 1 ||
          engine.history.size != 3 ||
          engine.chronology != #[.instance 0, .fact 0, .fact 1, .fact 2] then
        none
      else
        pure ()
      let instanceEvent <- engine.instanceHistory[0]?
      let instanceEntry <- session.arena.entry? instanceEvent.payload .instance
      let sineEvent <- engine.history[0]?
      let negationEvent <- engine.history[1]?
      let transportEvent <- engine.history[2]?
      let sine <- ruleStep? engine session.arena sineEvent
      let negation <- ruleStep? engine session.arena negationEvent
      let transport <- transportStep? engine session.arena transportEvent
      pure
        { instantiation :=
            { event := instanceEvent
              payload := instanceEvent.payload
              entry := instanceEntry }
          sine
          negation
          transport }

private def listExpr (type : Expr) (items : List Expr) : Expr :=
  items.foldr
    (fun item tail =>
      mkApp3 (mkConst ``List.cons [Level.zero]) type item tail)
    (mkApp (mkConst ``List.nil [Level.zero]) type)

private def natOptionExpr : Option Nat -> Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Nat)
  | some value =>
      mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Nat) (mkNatLit value)

private meta def nodeExpr (node : NodeId) : MetaM Expr :=
  do mkAppM ``NodeId.mk #[mkNatLit node.index]

private meta def ruleKeyExpr (key : RuleKey) : MetaM Expr :=
  do mkAppM ``RuleKey.mk #[toExpr key.name, mkNatLit key.schema]

private meta def ruleExpr (rule : RuleId) : MetaM Expr :=
  do mkAppM ``RuleId.mk #[mkNatLit rule.index]

private meta def applicationExpr (application : ApplicationId) : MetaM Expr :=
  do mkAppM ``ApplicationId.mk #[mkNatLit application.index]

private meta def equalityExpr (equality : EqualityId) : MetaM Expr :=
  do mkAppM ``EqualityId.mk #[mkNatLit equality.index]

private meta def payloadExpr (payload : PayloadId) : MetaM Expr :=
  do mkAppM ``PayloadId.mk #[mkNatLit payload.index]

private def actionKindExpr : ActionKind -> Expr
  | .forward => mkConst ``ActionKind.forward
  | .backward => mkConst ``ActionKind.backward
  | .improve => mkConst ``ActionKind.improve
  | .shave => mkConst ``ActionKind.shave
  | .instantiate => mkConst ``ActionKind.instantiate
  | .rewrite => mkConst ``ActionKind.rewrite
  | .regularize => mkConst ``ActionKind.regularize
  | .split => mkConst ``ActionKind.split

private meta def seenExpr (seen : SeenVersion) : MetaM Expr :=
  do mkAppM ``SeenVersion.mk #[← nodeExpr seen.node, mkNatLit seen.version]

private meta def structuralKeyExpr : StructuralKey -> MetaM Expr
  | .node node => do mkAppM ``StructuralKey.node #[← nodeExpr node]
  | .equality equality =>
      do mkAppM ``StructuralKey.equality #[← equalityExpr equality]
  | .application application =>
      do mkAppM ``StructuralKey.application #[← applicationExpr application]

private meta def structuralInputExpr (input : StructuralInput) : MetaM Expr :=
  do
    mkAppM ``StructuralInput.mk
      #[← structuralKeyExpr input.key, mkNatLit input.generation]

private meta def scopeExpr (binding : ScopeBinding) : MetaM Expr :=
  do
    mkAppM ``ScopeBinding.mk
      #[← ruleKeyExpr binding.rule,
      ← nodeExpr binding.anchor,
      listExpr (mkConst ``NodeId) (← binding.watches.mapM nodeExpr),
      listExpr (mkConst ``NodeId) (← binding.writes.mapM nodeExpr)]

private meta def actionExpr (action : Action) : MetaM Expr :=
  do
    mkAppM ``Action.mk
      #[mkNatLit action.serial,
      mkNatLit action.programVersion,
      ← applicationExpr action.application,
      ← ruleExpr action.rule,
      ← ruleKeyExpr action.key,
      ← nodeExpr action.node,
      actionKindExpr action.kind,
      mkNatLit action.effort,
      mkNatLit action.generation,
      listExpr (mkConst ``SeenVersion) (← action.inputs.mapM seenExpr),
      listExpr (mkConst ``NodeId) (← action.writes.mapM nodeExpr),
      listExpr (mkConst ``StructuralInput)
        (← action.structuralInputs.mapM structuralInputExpr),
      natOptionExpr action.matcherEpoch]

private def roleExpr : Role -> Expr
  | .fact => mkConst ``Role.fact
  | .instance => mkConst ``Role.instance
  | .equality => mkConst ``Role.equality

private meta def entryExpr (entry : Entry) : MetaM Expr :=
  do
    mkAppM ``Entry.mk
      #[← actionExpr entry.origin,
      roleExpr entry.role,
      mkNatLit entry.schema,
      listExpr (mkConst ``Nat) (entry.body.map mkNatLit)]

private def rangeExpr : Range -> Expr
  | .all => mkConst ``Range.all
  | .unit => mkConst ``Range.unit
  | .nonnegative => mkConst ``Range.nonnegative
  | .nonpositive => mkConst ``Range.nonpositive
  | .zero => mkConst ``Range.zero
  | .empty => mkConst ``Range.empty

private meta def factCauseExpr : FactCause Range -> MetaM Expr
  | .rule action proposed payload =>
      do
        mkAppM ``FactCause.rule
          #[← actionExpr action, rangeExpr proposed, ← payloadExpr payload]
  | .transport equality source =>
      do
        let equalityTerm <- equalityExpr equality
        let sourceTerm <- seenExpr source
        pure <|
          mkApp3 (mkConst ``FactCause.transport) (mkConst ``Range)
            equalityTerm sourceTerm

private meta def factEventExpr (event : FactEvent Range) : MetaM Expr :=
  do
    mkAppM ``FactEvent.mk
      #[mkNatLit event.programVersion,
      ← nodeExpr event.node,
      ← seenExpr event.previous,
      rangeExpr event.fact,
      mkNatLit event.version,
      ← factCauseExpr event.cause]

private meta def nodeFactExpr (fact : NodeFact Range) : MetaM Expr :=
  do mkAppM ``NodeFact.mk #[← nodeExpr fact.node, rangeExpr fact.fact]

private meta def edgeExpr (edge : EqualityEdge) : MetaM Expr :=
  do
    mkAppM ``EqualityEdge.mk
      #[← nodeExpr edge.left,
      ← nodeExpr edge.right,
      mkNatLit edge.generation,
      ← actionExpr edge.origin,
      ← payloadExpr edge.payload]

private meta def instanceEventExpr (event : InstanceEvent) : MetaM Expr :=
  do
    mkAppM ``InstanceEvent.mk
      #[mkNatLit event.programVersion,
      ← actionExpr event.origin,
      mkNatLit event.family,
      listExpr (mkConst ``NodeId) (← event.substitution.mapM nodeExpr),
      listExpr (mkConst ``NodeId) (← event.products.mapM nodeExpr),
      listExpr (mkConst ``NodeId) (← event.newNodes.mapM nodeExpr),
      listExpr (mkConst ``ScopeBinding) (← event.bindings.mapM scopeExpr),
      listExpr (mkConst ``ScopeBinding) (← event.newBindings.mapM scopeExpr),
      listExpr (mkConst ``ApplicationId) (← event.applications.mapM applicationExpr),
      listExpr (mkConst ``ApplicationId) (← event.newApplications.mapM applicationExpr),
      mkNatLit event.generation,
      listExpr (mkConst ``EqualityId) (← event.equalities.mapM equalityExpr),
      listExpr (mkConst ``EqualityId) (← event.newEqualities.mapM equalityExpr),
      ← payloadExpr event.payload]

private meta def instanceQuoteExpr (quote : InstanceQuote) : MetaM Expr :=
  do
    mkAppM ``InstanceQuote.mk
      #[← instanceEventExpr quote.event,
      ← payloadExpr quote.payload,
      ← entryExpr quote.entry]

private meta def ruleStepExpr (step : RuleStep Range) : MetaM Expr :=
  do
    let factType <- mkAppM ``NodeFact #[mkConst ``Range]
    mkAppM ``RuleStep.mk
      #[← factEventExpr step.event,
      ← payloadExpr step.payload,
      ← entryExpr step.entry,
      listExpr factType (← step.assumptions.mapM nodeFactExpr),
      rangeExpr step.previous]

private meta def transportStepExpr (step : TransportStep Range) : MetaM Expr :=
  do
    let factType <- mkAppM ``NodeFact #[mkConst ``Range]
    mkAppM ``TransportStep.mk
      #[← factEventExpr step.event,
      ← equalityExpr step.equality,
      ← edgeExpr step.edge,
      ← payloadExpr step.payload,
      ← entryExpr step.entry,
      listExpr factType (← step.assumptions.mapM nodeFactExpr),
      rangeExpr step.previous,
      rangeExpr step.sourceFact]

private meta def checkQuote (label : String) (actual expected : Expr) : MetaM Unit := do
  unless <- isDefEq actual expected do
    throwError "interval_sine: reified {label} does not match its checked proof step"

private meta def checkSchema (table : SchemaTable Name) (label : String)
    (entry : Entry) (expected : Name) : MetaM Unit := do
  let some declaration := table.find? entry.replayKey
    | throwError "interval_sine: no proof schema for {label}"
  unless declaration == expected do
    throwError "interval_sine: wrong proof schema selected for {label}"
  discard <| getConstInfo declaration

private meta def checkQuoteData (quote : LiveQuotes) : MetaM Unit := do
  let some table := emitTable?
    | throwError "interval_sine: duplicate proof-schema address"
  checkSchema table "instantiation" quote.instantiation.entry
    ``oddnessInstanceSchema
  checkSchema table "sine rule" quote.sine.entry ``sineFactSchema
  checkSchema table "negation rule" quote.negation.entry ``negationFactSchema
  checkSchema table "equality transport" quote.transport.entry
    ``oddnessEqualitySchema
  checkQuote "instantiation" (← instanceQuoteExpr quote.instantiation)
    (mkConst ``instanceQuote)
  checkQuote "sine rule" (← ruleStepExpr quote.sine) (mkConst ``sineStep)
  checkQuote "negation rule" (← ruleStepExpr quote.negation)
    (mkConst ``negationStep)
  checkQuote "equality transport" (← transportStepExpr quote.transport)
    (mkConst ``transportStep)

/-- Reify the planner's returned data and bind it to the proof-side literals.
This comparison is a liveness/fidelity gate, not evidence for the theorem. -/
private meta def checkLiveQuote : MetaM Unit := do
  let some quote := liveQuotes?
    | throwError "interval_sine: compiled interval search failed"
  checkQuoteData quote

/-- Find two local hypotheses accepted by the emitted sine theorem and build
an application whose inferred target is definitionally the caller's goal. -/
private meta def proveSine (target : Expr) : MetaM Expr := do
  let context <- getLCtx
  for first in context do
    unless first.isImplementationDetail do
      for second in context do
        unless second.isImplementationDetail do
          match ← observing? do
              let proof <- mkAppM ``emittedSineTheorem
                #[mkFVar first.fvarId, mkFVar second.fvarId]
              unless ← isDefEq (← inferType proof) target do
                throwError "candidate does not match the target"
              pure (← instantiateMVars proof) with
          | some proof =>
              checkLiveQuote
              return proof
          | none => pure ()
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

example {x : ℝ} (upper : x ≤ 1) (lower : 0 ≤ x) : Real.sin (-x) ≤ 0 := by
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
    if (← observing? (checkQuoteData malformed)).isSome then
      throwError "interval_sine test: malformed quote was accepted"
    let some table := emitTable?
      | throwError "interval_sine test: duplicate schema address"
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
