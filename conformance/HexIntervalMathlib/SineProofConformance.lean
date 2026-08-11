/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.ProofEmitter
import HexIntervalMathlib.SineSignConformance

/-!
# Ordinary proof emission for the real sine vertical

This file quotes every proof-producing event from the live `sin (-x)` search
as plain data.  The ordinary theorem depends only on transparent replay of
those literals through package-owned schemas.  The executable comparison with
the opaque session is a regression test for the tactic-side quotation code; it
is not an oracle used by the proof.
-/

namespace Hex.IntervalMathlib.SineProofConformance

open Hex.Interval.Experiment
open Propagator PayloadArena SemanticReplay ChronologicalReplay ProofEmitter
open SineSign SineSignConformance

def emitTable? : Option (SchemaTable Lean.Name) :=
  fixture?.map (fun fixture => fixture.registry.emit)

#guard
  emitTable?.any fun table =>
    table.find? sineFactSchema.key == some ``sineFactSchema &&
      table.find? negationFactSchema.key == some ``negationFactSchema &&
      table.find? oddnessInstanceSchema.key == some ``oddnessInstanceSchema &&
      table.find? oddnessEqualitySchema.key == some ``oddnessEqualitySchema

#guard (SchemaTable.build [sineEmit, sineEmit]).isNone
#guard
  (SchemaTable.build [negationEmit]).any fun table =>
    (table.find? negationFactSchema.key).isSome &&
      (table.find? sineFactSchema.key).isNone

def wrongSineEmit : EmitPackage Lean.Name :=
  { schemas :=
      [{ key := sineFactSchema.key
         handle := ``negationFactSchema },
       { key := oddnessInstanceSchema.key
         handle := ``oddnessInstanceSchema },
       { key := oddnessEqualitySchema.key
         handle := ``oddnessEqualitySchema }] }

#guard
  (SchemaTable.build [negationEmit, wrongSineEmit]).any fun table =>
    table.find? sineFactSchema.key == some ``negationFactSchema

def oddnessAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 2 }
    rule := { index := 2 }
    key := oddnessRuleKey
    node := node 2
    kind := .instantiate
    effort := 0
    generation := 0
    inputs := []
    writes := []
    structuralInputs :=
      [{ key := .node (node 0), generation := 0 },
       { key := .node (node 1), generation := 0 },
       { key := .node (node 2), generation := 0 },
       { key := .application { index := 0 }, generation := 0 },
       { key := .application { index := 1 }, generation := 0 },
       { key := .application { index := 2 }, generation := 0 }]
    matcherEpoch := some 0 }

def instanceEvent : InstanceEvent :=
  { programVersion := 1
    origin := oddnessAction
    family := 1
    substitution := [node 2]
    products := [node 3, node 4]
    newNodes := [node 3, node 4]
    generation := 1
    equalities := [{ index := 0 }]
    newEqualities := [{ index := 0 }]
    payload := payload 0 }

def instanceEntry : Entry :=
  { origin := oddnessAction
    role := .instance
    schema := 1
    body := [1] }

def instanceQuote : InstanceQuote :=
  { event := instanceEvent
    payload := payload 0
    entry := instanceEntry }

def sineAction : Action :=
  { serial := 1
    programVersion := 1
    application := { index := 3 }
    rule := { index := 1 }
    key := sineRuleKey
    node := node 3
    kind := .forward
    effort := 0
    generation := 1
    inputs := [{ node := node 0, version := 0 }]
    writes := [node 3] }

def sineEntry : Entry :=
  { origin := sineAction
    role := .fact
    schema := 1
    body := [Range.nonnegative.code] }

def sineStep : RuleStep Range :=
  { event :=
      { programVersion := 1
        node := node 3
        previous := { node := node 3, version := 0 }
        fact := .nonnegative
        version := 1
        cause := .rule sineAction .nonnegative (payload 2) }
    payload := payload 2
    entry := sineEntry
    assumptions := [{ node := node 0, fact := .unit }]
    previous := .all }

def negationAction : Action :=
  { serial := 2
    programVersion := 1
    application := { index := 4 }
    rule := { index := 0 }
    key := negationRuleKey
    node := node 4
    kind := .forward
    effort := 0
    generation := 1
    inputs := [{ node := node 3, version := 1 }]
    writes := [node 4] }

def negationEntry : Entry :=
  { origin := negationAction
    role := .fact
    schema := 1
    body := [Range.nonpositive.code] }

def negationStep : RuleStep Range :=
  { event :=
      { programVersion := 1
        node := node 4
        previous := { node := node 4, version := 0 }
        fact := .nonpositive
        version := 1
        cause := .rule negationAction .nonpositive (payload 3) }
    payload := payload 3
    entry := negationEntry
    assumptions := [{ node := node 3, fact := .nonnegative }]
    previous := .all }

def equalityEdge : EqualityEdge :=
  { left := node 2
    right := node 4
    generation := 1
    origin := oddnessAction
    payload := payload 1 }

def equalityEntry : Entry :=
  { origin := oddnessAction
    role := .equality
    schema := 1
    body := [1] }

def transportStep : TransportStep Range :=
  { event :=
      { programVersion := 1
        node := node 2
        previous := { node := node 2, version := 0 }
        fact := .nonpositive
        version := 1
        cause := .transport { index := 0 } { node := node 4, version := 1 } }
    equality := { index := 0 }
    edge := equalityEdge
    payload := payload 1
    entry := equalityEntry
    assumptions := []
    previous := .all
    sourceFact := .nonpositive }

def instanceReplay :=
  ProofEmitter.replayInstance oddnessInstanceSchema checkerInput 0 baseProgram
    extendedProgram (ProgramPrefix.refl baseProgram) programPrefix (by rfl)
    instanceQuote (extendRefl semantics baseProgram)

def malformedInstance : InstanceQuote :=
  { instanceQuote with payload := payload 99 }

def rejectedInstance :=
  ProofEmitter.replayInstance oddnessInstanceSchema checkerInput 0 baseProgram
    extendedProgram (ProgramPrefix.refl baseProgram) programPrefix (by rfl)
    malformedInstance (extendRefl semantics baseProgram)

#guard rejectedInstance.isNone

def emittedExtension : Evidence (semantics.Extends baseProgram extendedProgram) :=
  instanceReplay.get (by rfl)

theorem basePrefix : ProgramPrefix baseProgram baseProgram :=
  ProgramPrefix.refl baseProgram

theorem sameOperations : baseProgram.operations = extendedProgram.operations := by
  rfl

def initialExtension : Evidence (semantics.Extends baseProgram baseProgram) :=
  extendRefl semantics baseProgram

def sineBase :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 0, fact := .unit }) :=
  ProofEmitter.assumed (by simp [baseFacts])

def sinePrevious :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 3, fact := sineStep.previous }) := by
  simpa [sineStep, rangeSchema] using
    (ProofEmitter.topFact rangeSchema extendedProgram baseFacts (node 3)
      sineSourceInstruction (by rfl))

def sinePremises :
    EntailsList semantics extendedProgram baseFacts sineStep.assumptions :=
  .cons sineBase .nil

def sineInputs :
    Evidence
      (InputsSound semantics extendedProgram baseFacts sineStep.assumptions) :=
  sinePremises.sound

def sineReplay :=
  ProofEmitter.replayRule sineFactSchema rangeSchema checkerInput extendedProgram
    programPrefix baseFacts sineStep sinePrevious sineInputs

def emittedSine :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 3, fact := .nonnegative }) :=
  sineReplay.get (by rfl)

def negationPrevious :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 4, fact := negationStep.previous }) := by
  simpa [negationStep, rangeSchema] using
    (ProofEmitter.topFact rangeSchema extendedProgram baseFacts (node 4)
      negatedSineInstruction (by rfl))

def negationPremises :
    EntailsList semantics extendedProgram baseFacts negationStep.assumptions :=
  .cons emittedSine .nil

def negationInputs :
    Evidence
      (InputsSound semantics extendedProgram baseFacts negationStep.assumptions) :=
  negationPremises.sound

def negationReplay :=
  ProofEmitter.replayRule negationFactSchema rangeSchema checkerInput
    extendedProgram programPrefix baseFacts negationStep
    negationPrevious negationInputs

def emittedNegation :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 4, fact := .nonpositive }) :=
  negationReplay.get (by rfl)

def transportPrevious :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 2, fact := transportStep.previous }) := by
  apply ProofEmitter.assumed
  simp [transportStep, baseFacts]

def transportReplay :=
  ProofEmitter.replayTransport oddnessEqualitySchema rangeSchema laws checkerInput
    1 extendedProgram programPrefix baseFacts transportStep
    transportPrevious emittedNegation EntailsList.nil.sound

def malformedTransport : TransportStep Range :=
  { transportStep with payload := payload 99 }

def rejectedTransport :=
  ProofEmitter.replayTransport oddnessEqualitySchema rangeSchema laws checkerInput
    1 extendedProgram programPrefix baseFacts malformedTransport
    (by simpa [malformedTransport, transportStep] using transportPrevious)
    (by simpa [malformedTransport, transportStep] using emittedNegation)
    (by simpa [malformedTransport, transportStep] using noInputs)

#guard rejectedTransport.isNone

def emittedTransport :
    Evidence
      (semantics.Entails extendedProgram baseFacts
        { node := node 2, fact := .nonpositive }) :=
  transportReplay.get (by rfl)

/-- The complete emitted chain returns a theorem from the enlarged expression
network to the caller's original graph. -/
def emittedTarget :
    Evidence (semantics.Entails baseProgram baseFacts checkerInput.target) :=
  closeBase (input := checkerInput) stable baseWithin
    (by simp [checkerInput, baseProgram, node]) emittedExtension emittedTransport

theorem targetWithin : checkerInput.target.node.index < baseProgram.nodes.size := by
  simp [checkerInput, baseProgram, node]

/-- Close any dynamically assembled final evidence through the fixed
caller-program semantics bridge. -/
def closeEvidence
    (extension : Evidence (semantics.Extends baseProgram extendedProgram))
    (final :
      Evidence
        (semantics.Entails extendedProgram baseFacts checkerInput.target)) :
    Evidence (semantics.Entails baseProgram baseFacts checkerInput.target) :=
  closeBase (input := checkerInput) stable baseWithin targetWithin extension final

def sameEntry (left right : Entry) : Bool :=
  left.origin == right.origin && left.role == right.role &&
    left.schema == right.schema && left.body == right.body

/-- The literals agree field-for-field with the actual opaque search result.
This checks quotation fidelity only; `emittedTarget` does not depend on it. -/
def quotesMatchSearch : Bool :=
  match transported? with
  | none => false
  | some session =>
      match session.state.engine.instanceHistory[0]?,
          session.state.engine.equalities[0]?, session.state.engine.history[0]?,
          session.state.engine.history[1]?, session.state.engine.history[2]?,
          session.arena.entry? (payload 0) .instance,
          session.arena.entry? (payload 1) .equality,
          session.arena.entry? (payload 2) .fact,
          session.arena.entry? (payload 3) .fact with
      | some actualInstance, some actualEdge, some actualSine,
          some actualNegation, some actualTransport, some actualInstanceEntry,
          some actualEqualityEntry, some actualSineEntry, some actualNegationEntry =>
          actualInstance.programVersion == instanceEvent.programVersion &&
            actualInstance.origin == instanceEvent.origin &&
            actualInstance.family == instanceEvent.family &&
            actualInstance.substitution == instanceEvent.substitution &&
            actualInstance.products == instanceEvent.products &&
            actualInstance.newNodes == instanceEvent.newNodes &&
            actualInstance.bindings == instanceEvent.bindings &&
            actualInstance.newBindings == instanceEvent.newBindings &&
            actualInstance.applications == instanceEvent.applications &&
            actualInstance.newApplications == instanceEvent.newApplications &&
            actualInstance.generation == instanceEvent.generation &&
            actualInstance.equalities == instanceEvent.equalities &&
            actualInstance.newEqualities == instanceEvent.newEqualities &&
            actualInstance.payload == instanceEvent.payload &&
            actualEdge.left == equalityEdge.left &&
            actualEdge.right == equalityEdge.right &&
            actualEdge.generation == equalityEdge.generation &&
            actualEdge.origin == equalityEdge.origin &&
            actualEdge.payload == equalityEdge.payload &&
            sameEntry actualInstanceEntry instanceEntry &&
            sameEntry actualEqualityEntry equalityEntry &&
            sameEntry actualSineEntry sineEntry &&
            sameEntry actualNegationEntry negationEntry &&
            match actualSine.cause, actualNegation.cause, actualTransport.cause with
            | .rule action proposed payloadId,
                .rule negation proposedNegation negationPayload,
                .transport equality source =>
                actualSine.programVersion == sineStep.event.programVersion &&
                  actualSine.node == sineStep.event.node &&
                  actualSine.previous == sineStep.event.previous &&
                  actualSine.fact == sineStep.event.fact &&
                  actualSine.version == sineStep.event.version &&
                  action == sineAction && proposed == .nonnegative &&
                  payloadId == payload 2 &&
                  actualNegation.programVersion == negationStep.event.programVersion &&
                  actualNegation.node == negationStep.event.node &&
                  actualNegation.previous == negationStep.event.previous &&
                  actualNegation.fact == negationStep.event.fact &&
                  actualNegation.version == negationStep.event.version &&
                  negation == negationAction && proposedNegation == .nonpositive &&
                  negationPayload == payload 3 &&
                  actualTransport.programVersion == transportStep.event.programVersion &&
                  actualTransport.node == transportStep.event.node &&
                  actualTransport.previous == transportStep.event.previous &&
                  actualTransport.fact == transportStep.event.fact &&
                  actualTransport.version == transportStep.event.version &&
                  equality == transportStep.equality &&
                  source == ({ node := node 4, version := 1 } : SeenVersion)
            | _, _, _ => false
      | _, _, _, _, _, _, _, _, _ => false

#guard quotesMatchSearch

/-- Interpret any checked target evidence as the end-user sine theorem.  This
is the stable semantics bridge used after a tactic assembles replay evidence;
it does not depend on a particular event trace. -/
theorem closeSine
    (result : Evidence (semantics.Entails baseProgram baseFacts checkerInput.target))
    {x : ℝ} (nonnegative : 0 ≤ x)
    (atMostOne : x ≤ 1) : Real.sin (-x) ≤ 0 := by
  have target := result.proof (baseValuation x) (baseModels x) (by
    intro assumption member
    simp only [baseFacts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨nonnegative, atMostOne⟩
    · trivial
    · trivial)
  exact target

/-- End-user theorem obtained from the literal complete engine trace through
transparent replay.  Every `Option.get` above is justified by `rfl`; no
evaluator or Boolean guard participates in this proof. -/
theorem emittedSineTheorem {x : ℝ} (nonnegative : 0 ≤ x)
    (atMostOne : x ≤ 1) : Real.sin (-x) ≤ 0 :=
  closeSine emittedTarget nonnegative atMostOne

end Hex.IntervalMathlib.SineProofConformance
