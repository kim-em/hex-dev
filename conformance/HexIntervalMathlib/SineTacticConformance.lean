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
open SineSign SineSignConformance SineProofConformance

private structure LiveQuotes where
  instantiation : InstanceQuote
  sine : RuleStep Range
  negation : RuleStep Range
  transport : TransportStep Range

/-- Proof-producing event shapes extracted from arbitrary engine chronology. -/
private inductive LiveEvent where
  | instantiation (quote : InstanceQuote)
  | rule (step : RuleStep Range)
  | transport (step : TransportStep Range)

private structure LiveTrace where
  program : Program
  events : List LiveEvent

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

/-- Walk the engine's cross-history chronology once, requiring exact
sequential indices and complete fact/instance exhaustion. -/
private def quoteChronology? (engine : Engine Range) (arena : Arena) :
    List HistoryEvent -> Nat -> Nat -> Option (List LiveEvent)
  | [], nextFact, nextInstance =>
      if nextFact == engine.history.size &&
          nextInstance == engine.instanceHistory.size then
        some []
      else
        none
  | .instance index :: rest, nextFact, nextInstance => do
      if index != nextInstance then none else pure ()
      let event <- engine.instanceHistory[index]?
      let entry <- arena.entry? event.payload .instance
      let tail <- quoteChronology? engine arena rest nextFact (nextInstance + 1)
      pure
        (.instantiation
          { event
            payload := event.payload
            entry } :: tail)
  | .fact index :: rest, nextFact, nextInstance => do
      if index != nextFact then none else pure ()
      let event <- engine.history[index]?
      let head <-
        match event.cause with
        | .rule _ _ _ => (ruleStep? engine arena event).map .rule
        | .transport _ _ => (transportStep? engine arena event).map .transport
      let tail <- quoteChronology? engine arena rest (nextFact + 1) nextInstance
      pure (head :: tail)

/-- Extract the complete proof-event list from the actual returned state. -/
private def liveTrace? : Option LiveTrace :=
  match transported? with
  | none => none
  | some session => do
      let engine := session.state.engine
      if !session.live || session.droppedWork || engine.equalities.size != 1 then
        none
      else
        pure ()
      let events <-
        quoteChronology? engine session.arena engine.chronology.toList 0 0
      pure { program := engine.program, events }

/-- Specialize the generic quote to the literal-regression fixture. -/
private def liveQuotes? : Option LiveQuotes := do
  let trace <- liveTrace?
  let [.instantiation instantiation, .rule sine, .rule negation,
      .transport transport] := trace.events | none
  pure { instantiation, sine, negation, transport }

#guard
  transported?.any fun session =>
    let engine := session.state.engine
    (quoteChronology? engine session.arena engine.chronology.toList 0 0).isSome &&
      (quoteChronology? engine session.arena
        [.instance 0, .fact 0, .fact 0, .fact 2] 0 0).isNone &&
      (quoteChronology? engine session.arena
        [.instance 0, .fact 0, .fact 1] 0 0).isNone

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

private meta def domainExpr (domain : DomainId) : MetaM Expr :=
  do mkAppM ``DomainId.mk #[mkNatLit domain.index]

private meta def opExpr (operation : OpId) : MetaM Expr :=
  do mkAppM ``OpId.mk #[mkNatLit operation.index]

private meta def opKeyExpr (key : OpKey) : MetaM Expr :=
  do mkAppM ``OpKey.mk #[toExpr key.name, mkNatLit key.version]

private meta def operationExpr (operation : Operation) : MetaM Expr := do
  mkAppM ``Operation.mk
    #[← opKeyExpr operation.key,
      listExpr (mkConst ``DomainId) (← operation.inputs.mapM domainExpr),
      ← domainExpr operation.output]

private meta def instructionExpr (instruction : Node) : MetaM Expr := do
  mkAppM ``Node.mk
    #[← domainExpr instruction.domain,
      ← opExpr instruction.op,
      listExpr (mkConst ``NodeId) (← instruction.args.mapM nodeExpr)]

private meta def arrayExpr (type : Expr) (items : List Expr) : MetaM Expr :=
  mkAppM ``Array.mk #[listExpr type items]

private meta def programExpr (program : Program) : MetaM Expr := do
  mkAppM ``Program.mk
    #[← arrayExpr (mkConst ``Operation)
        (← program.operations.toList.mapM operationExpr),
      ← arrayExpr (mkConst ``Node)
        (← program.nodes.toList.mapM instructionExpr)]

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
  checkQuote "instantiation" (← instanceQuoteExpr quote.instantiation)
    (mkConst ``instanceQuote)
  checkQuote "sine rule" (← ruleStepExpr quote.sine) (mkConst ``sineStep)
  checkQuote "negation rule" (← ruleStepExpr quote.negation)
    (mkConst ``negationStep)
  checkQuote "equality transport" (← transportStepExpr quote.transport)
    (mkConst ``transportStep)

private meta def getReplay (result : Expr) : MetaM Expr := do
  let success <- mkAppM ``Eq.refl #[mkConst ``Bool.true]
  mkAppM ``Option.get #[result, success]

/-- Specialize generic caller-assumption seeding to this semantics adapter;
the elaborator still supplies the program, base list, index, and fact. -/
private def seedAssumed (program : Program) (base : List (NodeFact Range))
    (index : Nat) (fact : NodeFact Range) (found : base[index]? = some fact) :
    Evidence (semantics.Entails program base fact) :=
  ProofEmitter.assumedAt program base index fact found

private theorem checkedProgram (program : Program)
    (checked : program.check = true) :
    program.check = true :=
  checked

/-- One kernel proof already available at an exact engine fact version. -/
private structure FactProof where
  seen : SeenVersion
  fact : Range
  within : Expr
  proof : Expr

private def findFact? (known : List FactProof) (seen : SeenVersion)
    (fact : Range) : Option FactProof := do
  let item <- known.find? fun item => item.seen == seen
  if item.fact == fact then some item else none

private def findProof? (known : List FactProof) (seen : SeenVersion)
    (fact : Range) : Option Expr :=
  (findFact? known seen fact).map (fun item => item.proof)

private def insertProof (known : List FactProof) (item : FactProof) :
    MetaM (List FactProof) := do
  if known.any fun old => old.seen == item.seen then
    throwError "interval_sine: duplicate proof for a fact version"
  pure (item :: known)

/-- Assemble dependency evidence in the action's exact input order. -/
private meta def inputProofs (program : Expr) (known : List FactProof) :
    List SeenVersion -> List (NodeFact Range) -> MetaM Expr
  | [], [] =>
      mkAppM ``EntailsList.empty
        #[mkConst ``semantics, program, mkConst ``baseFacts]
  | seen :: seenTail, fact :: factTail => do
      unless seen.node == fact.node do
        throwError "interval_sine: input node does not match resolved fact"
      let some head := findProof? known seen fact.fact
        | throwError "interval_sine: input fact has not been proved yet"
      let tail <- inputProofs program known seenTail factTail
      mkAppM ``EntailsList.cons #[head, tail]
  | _, _ =>
      throwError "interval_sine: input versions and resolved facts differ in length"

private meta def soundInputs (program : Expr) (known : List FactProof)
    (seen : List SeenVersion) (facts : List (NodeFact Range)) : MetaM Expr := do
  let proofs <- inputProofs program known seen facts
  mkAppM ``EntailsList.sound #[proofs]

private meta def emitInstance (version : Nat) (before after : Expr)
    (basePrefix stepPrefix sameOperations : Expr) (quote : InstanceQuote)
    (previous : Expr) (table : SchemaTable Name) : MetaM Expr := do
  let schema <- schemaName table "instantiation" quote.entry
  let result <-
    mkAppM ``ProofEmitter.replayInstance
      #[mkConst schema,
        mkConst ``checkerInput,
        mkNatLit version,
        before,
        after,
        basePrefix,
        stepPrefix,
        sameOperations,
        ← instanceQuoteExpr quote,
        previous]
  getReplay result

/-- Derive caller-owned version-zero facts at the current program prefix. -/
private meta def seedBase (program : Expr) (basePrefix : Expr) :
    MetaM (List FactProof) := do
  let mut known := []
  let baseWithinProgram <-
    mkAppM ``ProofEmitter.liftFacts
      #[basePrefix, mkConst ``baseWithin]
  for (fact, index) in baseFacts.zipIdx do
    let factTerm <- nodeFactExpr fact
    let someFact <- mkAppM ``Option.some #[factTerm]
    let found <- mkAppM ``Eq.refl #[someFact]
    let proof <-
      mkAppM ``seedAssumed
        #[program, mkConst ``baseFacts, mkNatLit index, factTerm, found]
    let within <-
      mkAppM ``ProofEmitter.factWithinAt
        #[program, mkConst ``baseFacts, baseWithinProgram,
          mkNatLit index, factTerm, found]
    known <- insertProof known
      { seen := { node := fact.node, version := 0 }
        fact := fact.fact
        within
        proof }
  pure known

/-- Add domain-top proofs for exactly one instantiation's fresh node suffix. -/
private meta def seedNew (programValue : Program) (program : Expr)
    (newNodes : List NodeId) (known : List FactProof) :
    MetaM (List FactProof) := do
  let mut known := known
  for node in newNodes do
    let some instruction := programValue.node? node
      | throwError "interval_sine: fresh node is absent from the final program"
    let nodeTerm <- nodeExpr node
    let instructionTerm <- instructionExpr instruction
    let someInstruction <- mkAppM ``Option.some #[instructionTerm]
    let found <- mkAppM ``Eq.refl #[someInstruction]
    let proof <-
      mkAppM ``ProofEmitter.topFact
        #[mkConst ``rangeSchema, program, mkConst ``baseFacts,
          nodeTerm, instructionTerm, found]
    let within <-
      mkAppM ``ProofEmitter.nodeWithin
        #[program, nodeTerm, instructionTerm, found]
    known <- insertProof known
      { seen := { node, version := 0 }
        fact := rangeSchema.top instruction.domain
        within
        proof }
  pure known

/-- Dependent proof state carried through the quoted chronology.  `Expr`
fields are indexed by `program` in the kernel even though the elaborator keeps
their relationships dynamically. -/
private structure EmitState where
  version : Nat
  programValue : Program
  program : Expr
  snapshot : Expr
  basePrefix : Expr
  baseWithin : Expr
  extension : Expr
  known : List FactProof

private meta def initialSnapshot (finalProgram : Expr) : MetaM Expr := do
  let checked <- mkAppM ``Eq.refl #[mkConst ``Bool.true]
  let finalChecked <- mkAppM ``checkedProgram #[finalProgram, checked]
  let baseChecked <-
    mkAppM ``checkedProgram #[mkConst ``baseProgram, checked]
  mkAppM ``GenericInstanceReconstruction.Snapshot.mk
    #[finalChecked, baseChecked, mkConst ``programPrefix,
      mkConst ``sameOperations]

private meta def liftKnown (stable stepPrefix baseWithin : Expr)
    (known : List FactProof) : MetaM (List FactProof) :=
  known.mapM fun item => do
    let proof <-
      mkAppM ``ProofEmitter.liftFact
        #[stable, baseWithin, item.proof, item.within]
    let within <-
      mkAppM ``ProofEmitter.liftNode #[stepPrefix, item.within]
    pure { item with within, proof }

private meta def emitInstantiation (finalValue : Program) (finalProgram : Expr)
    (table : SchemaTable Name) (state : EmitState) (quote : InstanceQuote) :
    MetaM EmitState := do
  let event <- instanceEventExpr quote.event
  let reconstruction <-
    mkAppM ``GenericInstanceReconstruction.reconstruct?
      #[mkConst ``stableLaw, finalProgram, state.program, state.snapshot, event]
  let step <- getReplay reconstruction
  let after <-
    mkAppM ``GenericInstanceReconstruction.Step.after #[step]
  let stepPrefix <-
    mkAppM ``GenericInstanceReconstruction.Step.stepPrefix #[step]
  let stable <-
    mkAppM ``GenericInstanceReconstruction.Step.stable #[step]
  let sameOperations <-
    mkAppM ``GenericInstanceReconstruction.Step.sameOperations #[step]
  let nextSnapshot <-
    mkAppM ``GenericInstanceReconstruction.Step.next #[step]
  let extension <-
    emitInstance state.version state.program after state.basePrefix stepPrefix
      sameOperations quote state.extension table
  let known <- liftKnown stable stepPrefix state.baseWithin state.known
  let baseWithin <-
    mkAppM ``ProofEmitter.liftFacts #[stepPrefix, state.baseWithin]
  let basePrefix <-
    mkAppM ``ChronologicalReplay.prefixTrans #[state.basePrefix, stepPrefix]
  let nextSize := state.programValue.nodes.size + quote.event.newNodes.length
  let afterValue :=
    GenericInstanceReconstruction.programPrefix finalValue nextSize
  let known <- seedNew afterValue after quote.event.newNodes known
  pure
    { version := quote.event.programVersion
      programValue := afterValue
      program := after
      snapshot := nextSnapshot
      basePrefix
      baseWithin
      extension
      known }

private meta def emitRule (program basePrefix : Expr) (version : Nat)
    (table : SchemaTable Name) (known : List FactProof) (step : RuleStep Range) :
    MetaM (List FactProof) := do
  unless step.event.programVersion == version do
    throwError "interval_sine: rule event has the wrong program version"
  let .rule action _ _ := step.event.cause
    | throwError "interval_sine: rule quote has a transport cause"
  let some previous := findFact? known step.event.previous step.previous
    | throwError "interval_sine: rule previous fact has not been proved"
  let inputs <- soundInputs program known action.inputs step.assumptions
  let schema <- schemaName table "fact rule" step.entry
  let result <-
    mkAppM ``ProofEmitter.replayRule
      #[mkConst schema,
        mkConst ``rangeSchema,
        mkConst ``checkerInput,
        program,
        basePrefix,
        mkConst ``baseFacts,
        ← ruleStepExpr step,
        previous.proof,
        inputs]
  let proof <- getReplay result
  insertProof known
    { seen := { node := step.event.node, version := step.event.version }
      fact := step.event.fact
      within := previous.within
      proof }

private meta def emitTransport (program basePrefix : Expr) (version : Nat)
    (table : SchemaTable Name) (known : List FactProof)
    (step : TransportStep Range) :
    MetaM (List FactProof) := do
  unless step.event.programVersion == version do
    throwError "interval_sine: transport event has the wrong program version"
  let .transport _ source := step.event.cause
    | throwError "interval_sine: transport quote has a rule cause"
  let some previous := findFact? known step.event.previous step.previous
    | throwError "interval_sine: transport previous fact has not been proved"
  let some sourceProof := findProof? known source step.sourceFact
    | throwError "interval_sine: equality source fact has not been proved"
  let inputs <- soundInputs program known step.edge.origin.inputs step.assumptions
  let schema <- schemaName table "equality transport" step.entry
  let result <-
    mkAppM ``ProofEmitter.replayTransport
      #[mkConst schema,
        mkConst ``rangeSchema,
        mkConst ``laws,
        mkConst ``checkerInput,
        mkNatLit version,
        program,
        basePrefix,
        mkConst ``baseFacts,
        ← transportStepExpr step,
        previous.proof,
        sourceProof,
        inputs]
  let proof <- getReplay result
  insertProof known
    { seen := { node := step.event.node, version := step.event.version }
      fact := step.event.fact
      within := previous.within
      proof }

private meta def emitEvents (finalValue : Program) (finalProgram : Expr)
    (table : SchemaTable Name) :
    List LiveEvent -> EmitState -> MetaM EmitState
  | [], state => pure state
  | .instantiation quote :: rest, state => do
      let state <-
        emitInstantiation finalValue finalProgram table state quote
      emitEvents finalValue finalProgram table rest state
  | .rule step :: rest, state => do
      let known <-
        emitRule state.program state.basePrefix state.version table state.known step
      emitEvents finalValue finalProgram table rest { state with known }
  | .transport step :: rest, state => do
      let known <-
        emitTransport state.program state.basePrefix state.version table state.known step
      emitEvents finalValue finalProgram table rest { state with known }

/-- Emit a proof by folding arbitrary fact events through an exact
`(node, version)` evidence table and reconstructed program state.  The event
fold does not name any function or propagator; packages are selected only
through their replay addresses. -/
private meta def emitTrace (programValue : Program) (events : List LiveEvent)
    (table : SchemaTable Name) :
    MetaM Expr := do
  unless programValue.check do
    throwError "interval_sine: final expression program is not checked"
  let finalProgram <- programExpr programValue
  let snapshot <- initialSnapshot finalProgram
  let baseProgram := mkConst ``baseProgram
  let basePrefix := mkConst ``basePrefix
  let known <- seedBase baseProgram basePrefix
  let initial : EmitState :=
    { version := 0
      programValue := SineSign.baseProgram
      program := baseProgram
      snapshot
      basePrefix
      baseWithin := mkConst ``baseWithin
      extension := mkConst ``initialExtension
      known }
  let state <- emitEvents programValue finalProgram table events initial
  unless state.programValue == programValue do
    throwError "interval_sine: trace did not consume the complete final program"
  let target := { node := node 2, version := 1 : SeenVersion }
  let some final := findProof? state.known target .nonpositive
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

/--
info: 'Hex.IntervalMathlib.SineTacticConformance.tacticSine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tacticSine

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
    let reordered : List LiveEvent :=
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
    if (← observing? (emitTrace baseProgram
        [ .instantiation quote.instantiation, .rule quote.sine,
          .rule quote.negation, .transport quote.transport ] table)).isSome then
      throwError "interval_sine test: emission against the wrong final program was accepted"
    if (← observing?
        (seedNew baseProgram (mkConst ``baseProgram) [node 3] [])).isSome then
      throwError "interval_sine test: absent generated node received a top proof"
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
