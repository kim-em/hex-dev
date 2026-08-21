/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PolicySession
import HexInterval.Experiment.SemanticReplay

/-!
# Arbitrary-function package conformance through the policy session

This canary contains no interval representation or rational arithmetic.  A
function package recognizes `sin (-x)` in an engine-owned structural batch,
proposes `sin x` and `-(sin x)`, records their oddness equality, and installs a
dynamically scoped sine contractor.  An external policy selects that theorem
instance and then runs the new contractor, which improves the fact on `sin x`.
Proof recipes for the theorem instance, equality, and contraction are frozen
under their exact package handlers.

A companion negative case changes the contractor's watch from `x` to `-x`.
The proposal remains generically well-formed, but the sine package vetoes its
semantic scope and the session rolls back the proof arena, retained proposal,
and matcher cursor together.
-/

namespace Hex.Interval.PolicyFunctionConformance

local notation "OfferView" =>
  Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "Selection" =>
  Hex.Interval.Policy.Decision _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "ScopeId" => Hex.Interval.Policy.ScopeId
local notation "OfferClass" => Hex.Interval.Policy.OfferClass

open Experiment Propagator PayloadArena PolicySession SemanticReplay

abbrev Rank := Nat

def rankDomain : FactDomain Rank where
  top _ := 0
  narrow _ current proposed :=
    if current < proposed then .improved proposed else .noChange

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "policy-function.source" }
def negKey : OpKey := { name := "policy-function.neg" }
def sinKey : OpKey := { name := "policy-function.sin" }

def matcherKey : RuleKey := { name := "policy-function.sin-shapes" }
def contractKey : RuleKey := { name := "policy-function.sin-contract" }

def operations : Array Operation :=
  #[{ key := sourceKey, inputs := [], output := real },
    { key := negKey, inputs := [real], output := real },
    { key := sinKey, inputs := [real], output := real }]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def program : Program :=
  { operations
    nodes :=
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 1 }, args := [node 0] },
        { domain := real, op := { index := 2 }, args := [node 1] }] }

def matcherRule : Registration :=
  { key := matcherKey
    head := sinKey
    kind := .instantiate
    watches := []
    writes := []
    binding := .global
    watchesProgram := true
    matchWatch := .network }

def contractRule : Registration :=
  { key := contractKey
    head := sinKey
    kind := .improve
    watches := []
    writes := []
    binding := .scoped }

def instanceFormat : ReplayFormat :=
  { role := .instance
    schema := 4
    validateBody := fun body =>
      match body with
      | [_, 47] => true
      | _ => false }

def equalityFormat : ReplayFormat :=
  { role := .equality
    schema := 3
    validateBody := fun body => body == [43] }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 5
    validateBody := fun body => body == [1, 73] }

/-- Package-owned recognition of the expression shape `sin (-x)`. -/
def oddness? (view : ProgramView) (input : StructuralInput) :
    Option InstantiationRequest := do
  let .node anchor := input.key | none
  if view.operationKey? anchor != some sinKey then none else pure ()
  let expression <- view.node? anchor
  let [negated] := expression.args | none
  if view.operationKey? negated != some negKey then none else pure ()
  let negation <- view.node? negated
  let [argument] := negation.args | none
  let (sinId, _) <- view.findOp? sinKey
  let (negId, _) <- view.findOp? negKey
  pure
    { key := 41
      nodes :=
        [{ domain := real, op := sinId, args := [.existing argument] },
          { domain := real, op := negId, args := [.proposed 0] }]
      equalities :=
        [{ left := .existing anchor
           right := .proposed 1
           payload := payload 43 }]
      scopes :=
        [{ rule := contractKey
           anchor := .proposed 0
           watches := [.existing argument]
           writes := [.proposed 0] }]
      payload := payload 47 }

def rejectedOddness? (view : ProgramView) (input : StructuralInput) :
    Option InstantiationRequest := do
  let request <- oddness? view input
  pure
    { request with
      scopes :=
        [{ rule := contractKey
           anchor := .proposed 0
           watches := [.existing (node 1)]
           writes := [.proposed 0] }] }

def matcherPlanWith
    (recognize : ProgramView -> StructuralInput -> Option InstantiationRequest)
    (request : RuleRequest Rank) : Plan Rank :=
  match request.action.structuralInputs.findSome? (recognize request.program) with
  | none => { outcome := .noChange {}, drafts := [] }
  | some proposal =>
      { outcome := .success [] [.instantiate proposal] {}
        drafts :=
          [{ label := payload 47
             role := .instance
             schema := 4
             body := [request.action.structuralInputs.length, 47] },
           { label := payload 43
             role := .equality
             schema := 3
             body := [43] }] }

def matcherPlan : RuleRequest Rank -> Plan Rank :=
  matcherPlanWith oddness?

def rejectedMatcherPlan : RuleRequest Rank -> Plan Rank :=
  matcherPlanWith rejectedOddness?

/-- The dynamically installed arbitrary-function contractor. -/
def contractPlan (request : RuleRequest Rank) : Plan Rank :=
  match request.inputs, request.writes with
  | [_], [target] =>
      { outcome :=
          .success
            [{ node := target, fact := 1, payload := payload 73 }]
            [] {}
        drafts :=
          [{ label := payload 73
             role := .fact
             schema := 5
             body := [1, 73] }] }
  | _, _ => { outcome := .failed 7, drafts := [] }

/-- The sine package, rather than the generic engine, defines the semantic
shape of a valid dynamically scoped contractor. -/
def acceptsContract (actualProgram : Program) (binding : ScopeBinding) : Bool :=
  actualProgram.check && binding.rule == contractKey &&
    ((actualProgram.node? binding.anchor).any fun instruction =>
      (actualProgram.operation? instruction.op).any fun operation =>
        operation.key == sinKey && instruction.args == binding.watches) &&
    binding.writes == [binding.anchor]

def packageWith (plan : RuleRequest Rank -> Plan Rank) : Package Rank :=
  { Cache := Nat
    cache := 0
    operations
    handlers :=
      #[{ registration := matcherRule
          replayFormats := #[instanceFormat, equalityFormat]
          invoke := fun cache request =>
            (plan request, cache + request.action.structuralInputs.length) },
        { registration := contractRule
          replayFormats := #[factFormat]
          acceptsScope := acceptsContract
          invoke := fun cache request => (contractPlan request, cache + 1) }] }

def package : Package Rank := packageWith matcherPlan
def rejectedPackage : Package Rank := packageWith rejectedMatcherPlan

def engineLimits : Hex.Interval.State.Limits :=
  { maxOperations := 3
    maxNodes := 5
    maxRules := 2
    maxRegistryEntries := 12
    maxReplayFormats := 3
    maxArity := 1
    maxScopeNodes := 1
    maxApplications := 2
    maxQueueEntries := 8
    maxActions := 4
    maxMatcherVisits := 4
    matcherBatchSize := 4
    maxAcceptedFacts := 4
    maxRetainedSuggestions := 1
    maxEffort := 1
    maxObservationValue := 8
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 1
    maxProposalItems := 2
    maxInstances := 1
    maxGeneration := 1
    maxNodeDepth := 4
    maxEqualities := 1
    splitEndpointLimit :=
      { maxEndpointHeight := 8, maxAlignmentShift := 4 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8
    maxTraversal := 64
    maxLiveOffers := 8 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 8
    maxBodyCells := 16
    maxDrafts := 8
    maxDraftCells := 8
    maxAtom := 100
    maxSchema := 5
    maxUses := 8 }

def limits : PolicySession.Limits :=
  { engine := engineLimits
    policy := policyLimits
    arena := arenaLimits }

def start (candidate : Package Rank) :
    Except PolicySession.StartError (PolicySession.Session Rank) :=
  PolicySession.Session.start rankDomain program #[candidate] #[0, 0, 0] limits

def matcherInputs : List StructuralInput :=
  [{ key := .node (node 0), generation := 0 },
   { key := .node (node 1), generation := 0 },
   { key := .node (node 2), generation := 0 },
   { key := .application { index := 0 }, generation := 0 }]

def invokes (key : RuleKey) (offer : (Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey)) : Bool :=
  match offer.key with
  | .invoke invocation => invocation.rule == key
  | _ => false

def instantiatesMatcher (offer : (Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey)) : Bool :=
  match offer.key with
  | .instantiate source _ => source.rule == matcherKey
  | _ => false

def invocation? (session : PolicySession.Session Rank) (key : RuleKey) :
    Option
      ((Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) × (Hex.Interval.Policy.Decision _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) ×
        PolicySession.Session Rank) :=
  match session.view with
  | .ready view viewed =>
      match view.offers.toList.find? (invokes key) with
      | none => none
      | some offer =>
          some
            (offer,
              Hex.Interval.Policy.select view offer,
              viewed)
  | .resource _ _ | .contradiction _ | .invalidSession _ => none

def instantiation? (session : PolicySession.Session Rank) :
    Option
      ((Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) × (Hex.Interval.Policy.Decision _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) ×
        PolicySession.Session Rank) :=
  match session.view with
  | .ready view viewed =>
      match view.offers.toList.find? instantiatesMatcher with
      | none => none
      | some offer =>
          some
            (offer,
              Hex.Interval.Policy.select view offer,
              viewed)
  | .resource _ _ | .contradiction _ | .invalidSession _ => none

def matched? : Option (PolicySession.Session Rank) := do
  let .ok session := start package | none
  let (offer, selection, viewed) <- invocation? session matcherKey
  let .invoke invocation := offer.key | none
  if invocation.structuralInputs != matcherInputs ||
      invocation.matcherEpoch != some 0 then
    none
  else
    match viewed.choose (.select selection) with
    | .rule _ observation next =>
        if observation.invocation == invocation &&
            observation.outcome == .success &&
            observation.suggestionPlan.kept.length == 1 &&
            observation.emittedSuggestions.size == 1 then
          some next
        else
          none
    | _ => none

-- Matcher selection freezes both theorem recipes and commits the exact
-- engine-owned batch and retained instance in one session transition.
#guard
  match matched? with
  | none => false
  | some session =>
      session.live && !session.droppedWork &&
        session.arena.entries.size == 2 &&
        session.arena.bodyCells == 3 &&
        session.state.engine.suggestions.size == 1 &&
        session.state.engine.metrics.matcherVisits == 4 &&
        session.state.metrics.selectedInvocations == 1 &&
        match session.state.engine.matcherCursors[0]?,
            session.arena.entry? (payload 0) .instance,
            session.arena.entry? (payload 1) .equality,
            session.state.engine.suggestions[0]? with
        | some (some cursor), some instanceEntry, some equalityEntry,
            some retained =>
            cursor.offset == 4 && cursor.exhausted &&
              instanceEntry.replayKey ==
                { rule := matcherKey, role := .instance, schema := 4 } &&
              equalityEntry.replayKey ==
                { rule := matcherKey, role := .equality, schema := 3 } &&
              instanceEntry.origin.structuralInputs == matcherInputs &&
              equalityEntry.origin.structuralInputs == matcherInputs &&
              instanceEntry.origin.matcherEpoch == some 0 &&
              equalityEntry.origin.matcherEpoch == some 0 &&
              match retained.suggestion with
              | .instantiate request =>
                  request.payload == payload 0 &&
                    match request.equalities with
                    | [equality] => equality.payload == payload 1
                    | _ => false
              | _ => false
        | _, _, _, _ => false

def admitted? : Option (PolicySession.Session Rank) := do
  let session <- matched?
  let (_, selection, viewed) <- instantiation? session
  match viewed.choose (.select selection) with
  | .instance _ (.instanceAdmitted [sinX, negSinX]) next =>
      if sinX == node 3 && negSinX == node 4 then some next else none
  | _ => none

-- The policy-selected theorem instance atomically adds both expressions, its
-- equality, and the package-validated arbitrary contractor.
#guard
  match admitted? with
  | none => false
  | some session =>
      session.state.engine.programVersion == 1 &&
        session.state.engine.program.nodes.size == 5 &&
        session.state.engine.equalities.size == 1 &&
        session.state.engine.bindings.size == 1 &&
        session.state.engine.applications.size == 2 &&
        session.state.engine.instanceHistory.size == 1 &&
        session.state.engine.chronology == #[.instance 0] &&
        session.state.metrics.selectedInstances == 1 &&
        match session.state.engine.bindings[0]?,
            session.state.engine.equalities[0]?,
            session.state.engine.instanceHistory[0]? with
        | some binding, some equality, some event =>
            binding.rule == contractKey && binding.anchor == node 3 &&
              binding.watches == [node 0] && binding.writes == [node 3] &&
              equality.left == node 2 && equality.right == node 4 &&
              equality.payload == payload 1 && event.payload == payload 0 &&
              event.newNodes == [node 3, node 4] &&
              event.newEqualities == [{ index := 0 }] &&
              event.newBindings == [binding]
        | _, _, _ => false

def contracted? : Option (PolicySession.Session Rank) := do
  let session <- admitted?
  let (_, selection, viewed) <- invocation? session contractKey
  match viewed.choose (.select selection) with
  | .rule _ observation next =>
      if observation.invocation.rule == contractKey &&
          observation.outcome == .success &&
          observation.changes.size == 1 then
        some next
      else
        none
  | _ => none

-- The newly installed function propagator is not merely metadata: policy
-- selection invokes it, improves `sin x`, and freezes its own proof recipe.
#guard
  match contracted? with
  | none => false
  | some session =>
      session.state.engine.facts[3]? == some 1 &&
        session.state.engine.versions[3]? == some 1 &&
        session.state.engine.history.size == 1 &&
        session.state.engine.chronology == #[.instance 0, .fact 0] &&
        session.arena.entries.size == 3 &&
        session.arena.bodyCells == 5 &&
        session.state.metrics.selectedInvocations == 2 &&
        (session.registry.packages[0]?).any fun package =>
          package.invocations == 2 &&
            match session.arena.entry? (payload 2) .fact,
                session.state.engine.history[0]? with
            | some entry, some event =>
                entry.replayKey ==
                    { rule := contractKey, role := .fact, schema := 5 } &&
                  entry.body == [1, 73] &&
                  match event.cause with
                  | .rule action _ proof =>
                      action.key == contractKey &&
                        action.writes == [node 3] && proof == payload 2
                  | .transport _ _ => false
            | _, _ => false

/-! ## Package-owned semantic replay of the live function session -/

/-- The compact semantic canary interprets the package's sine-shaped operation
as the constant-zero function and its negation-shaped operation as integer
negation.  The generic replay registry never sees either interpretation. -/
def sinNegInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [node 1] }

def sinInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [node 0] }

def negSinInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 3] }

def extendedProgram : Program :=
  { operations
    nodes := program.nodes ++ #[sinInstruction, negSinInstruction] }

def FunctionModels (actualProgram : Program) (valuation : NodeId -> Int) : Prop :=
  (actualProgram.node? (node 2) = some sinNegInstruction ->
    valuation (node 2) = 0) ∧
  (actualProgram.node? (node 3) = some sinInstruction ->
    valuation (node 3) = 0) ∧
  (actualProgram.node? (node 4) = some negSinInstruction ->
    valuation (node 4) = -valuation (node 3))

def RankAllows (rank : Rank) (value : Int) : Prop :=
  rank = 0 ∨ value = 0

def functionSemantics : SemanticReplay.Semantics Rank :=
  { Value := Int
    models := FunctionModels
    holds := fun _ valuation fact => RankAllows fact.fact (valuation fact.node) }

theorem functionPrefix : ProgramPrefix program extendedProgram := by
  refine
    { operationSize := ?_
      nodeSize := ?_
      operationAt := ?_
      nodeAt := ?_ }
  · simp [program, extendedProgram]
  · simp [program, extendedProgram]
  · intro index within
    simp [program, extendedProgram]
  · intro index within
    cases index with
    | zero => rfl
    | succ index =>
        cases index with
        | zero => rfl
        | succ index =>
            cases index with
            | zero => rfl
            | succ index =>
                have lower : 3 ≤ index + 1 + 1 + 1 := by
                  exact Nat.le_add_left 3 index
                exact False.elim (Nat.not_lt_of_ge lower within)

/-- Adding the package-generated `sin x` and `-(sin x)` nodes is a
conservative semantic extension: every old valuation extends without changing
an old node. -/
theorem functionExtension :
    functionSemantics.Extends program extendedProgram := by
  intro valuation model
  let extended : NodeId -> Int :=
    fun observed => if observed.index < 3 then valuation observed else 0
  refine ⟨extended, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro _
      have old := model.1 (by rfl)
      simpa [extended, node] using old
    · intro _
      simp [extended, node]
    · intro _
      simp [extended, node]
  · intro observed within
    have oldIndex : observed.index < 3 := by
      simpa [program] using within
    simp [extended, oldIndex]

theorem oddnessEntails :
    functionSemantics.EntailsEq extendedProgram []
      (node 2) (node 4) := by
  change ∀ valuation : NodeId -> Int, FunctionModels extendedProgram valuation ->
    (∀ assumption, assumption ∈ ([] : List (NodeFact Rank)) ->
      RankAllows assumption.fact (valuation assumption.node)) ->
    valuation (node 2) = valuation (node 4)
  intro valuation model _
  have sinNeg := model.1 (by rfl)
  have sinX := model.2.1 (by rfl)
  have negSinX := model.2.2 (by rfl)
  calc
    valuation (node 2) = (0 : Int) := sinNeg
    _ = -valuation (node 3) := by rw [sinX]; simp
    _ = valuation (node 4) := negSinX.symm

theorem contractEntails (assumptions : List (NodeFact Rank)) :
    functionSemantics.Entails extendedProgram assumptions
      { node := node 3, fact := 1 } := by
  intro valuation model _
  exact Or.inr (model.2.1 (by rfl))

inductive InstanceCertificate where
  | oddness (batchSize : Nat)

inductive EqualityCertificate where
  | oddness

inductive FactCertificate where
  | range

def decodeInstance : List Nat -> Option InstanceCertificate
  | [batchSize, 47] => some (.oddness batchSize)
  | _ => none

def decodeEquality : List Nat -> Option EqualityCertificate
  | [43] => some .oddness
  | _ => none

def decodeFact : List Nat -> Option FactCertificate
  | [1, 73] => some .range
  | _ => none

def contractBinding : ScopeBinding :=
  { rule := contractKey
    anchor := node 3
    watches := [node 0]
    writes := [node 3] }

def instanceSchema : PackedInstanceSchema functionSemantics :=
  { rule := matcherKey
    schema := 4
    Certificate := InstanceCertificate
    decode := decodeInstance
    replay := fun _ _ context certificate =>
      if beforeProof : context.before = program then
        if afterProof : context.after = extendedProgram then
          if shapeProof :
              context.event.programVersion = 1 ∧
                context.event.family = 41 ∧
                context.event.substitution = [node 2] ∧
                context.event.products = [node 3, node 4] ∧
                context.event.newNodes = [node 3, node 4] ∧
                context.event.bindings = [contractBinding] ∧
                context.event.newBindings = [contractBinding] ∧
                context.event.applications = [{ index := 1 }] ∧
                context.event.newApplications = [{ index := 1 }] ∧
                context.event.generation = 1 ∧
                context.event.equalities = [{ index := 0 }] ∧
                context.event.newEqualities = [{ index := 0 }] ∧
                context.event.payload = payload 0 then
            match certificate with
            | .oddness batchSize =>
                if batchProof :
                    batchSize = context.event.origin.structuralInputs.length then
                  some
                    { proof := by
                        simpa [beforeProof, afterProof] using functionExtension }
                else none
          else none
        else none
      else none }

def equalitySchema : PackedEqualitySchema functionSemantics :=
  { rule := matcherKey
    schema := 3
    Certificate := EqualityCertificate
    decode := decodeEquality
    replay := fun _ _ context _ =>
      if programProof : context.program = extendedProgram then
        if shapeProof :
            context.assumptions = [] ∧
              context.equality = { index := 0 } ∧
              context.edge.left = node 2 ∧
              context.edge.right = node 4 ∧
              context.edge.generation = 1 ∧
              context.edge.payload = payload 1 then
          let assumptionsProof := shapeProof.1
          let leftProof := shapeProof.2.2.1
          let rightProof := shapeProof.2.2.2.1
          some
            { proof := by
                simpa [programProof, assumptionsProof, leftProof, rightProof]
                  using oddnessEntails }
        else none
      else none }

def factSchema : PackedFactSchema functionSemantics :=
  { rule := contractKey
    schema := 5
    Certificate := FactCertificate
    decode := decodeFact
    replay := fun _ action context _ =>
      if programProof : context.program = extendedProgram then
        if shapeProof :
            action.key = contractKey ∧
              context.proposed = { node := node 3, fact := 1 } then
          let proposedProof := shapeProof.2
          some
            { proof := by
                simpa [programProof, proposedProof] using
                  contractEntails context.assumptions }
        else none
      else none }

def functionProofs : SemanticReplay.Package functionSemantics :=
  { factSchemas := #[factSchema]
    instanceSchemas := #[instanceSchema]
    equalitySchemas := #[equalitySchema] }

def checkerInput : CheckerInput Rank :=
  { baseProgram := program
    initialFacts := #[0, 0, 0]
    target := { node := node 3, fact := 1 } }

structure SemanticFixture where
  session : PolicySession.Session Rank
  registry : SemanticReplay.Registry functionSemantics

def semanticFixture? : Option SemanticFixture := do
  let session ← contracted?
  let registry ←
    match SemanticReplay.Registry.build session.registry #[functionProofs] with
    | .ok registry => some registry
    | .error _ => none
  pure { session, registry }

def replaysFunctionSession : Bool :=
  match semanticFixture? with
  | none => false
  | some fixture =>
      let finalProgram := fixture.session.state.engine.program
      if finalProof : finalProgram = extendedProgram then
        let basePrefix : ProgramPrefix checkerInput.baseProgram finalProgram := by
          simpa [checkerInput, finalProof] using functionPrefix
        let stepPrefix : ProgramPrefix program finalProgram := by
          simpa [finalProof] using functionPrefix
        let sameOperations : program.operations = finalProgram.operations := by
          simp [finalProof, extendedProgram, program]
        match fixture.session.state.engine.instanceHistory[0]?,
            fixture.session.state.engine.equalities[0]?,
            fixture.session.state.engine.history[0]? with
        | some event, some edge, some factEvent =>
            let instanceProof :=
              fixture.registry.replayInstance checkerInput fixture.session.arena
                event program finalProgram (ProgramPrefix.refl program)
                stepPrefix sameOperations
            let equalityProof :=
              fixture.registry.replayEquality checkerInput fixture.session.arena
                { index := 0 } edge finalProgram basePrefix []
            let factReplayed :=
              match factEvent.cause with
              | .rule action proposed proof =>
                  (fixture.registry.replayRule checkerInput fixture.session.arena
                    action proposed proof finalProgram basePrefix
                    [{ node := node 0, fact := 0 }] factEvent.node).isSome
              | .transport _ _ => false
            instanceProof.isSome && equalityProof.isSome && factReplayed
        | _, _, _ => false
      else
        false

-- The actual matcher event, equality edge, and contractor fact event all
-- replay through package-owned theorem schemas.  No central function tag or
-- rational-arithmetic backend participates in this proof path.
#guard replaysFunctionSession

def replaysInstanceEvent (fixture : SemanticFixture)
    (arena : Arena) (event : InstanceEvent) : Bool :=
  let finalProgram := fixture.session.state.engine.program
  if finalProof : finalProgram = extendedProgram then
    let stepPrefix : ProgramPrefix program finalProgram := by
      simpa [finalProof] using functionPrefix
    let sameOperations : program.operations = finalProgram.operations := by
      simp [finalProof, extendedProgram, program]
    (fixture.registry.replayInstance checkerInput arena event program finalProgram
      (ProgramPrefix.refl program) stepPrefix sameOperations).isSome
  else
    false

def replaysEqualityEdge (fixture : SemanticFixture)
    (arena : Arena) (edge : EqualityEdge) : Bool :=
  let finalProgram := fixture.session.state.engine.program
  if finalProof : finalProgram = extendedProgram then
    let basePrefix : ProgramPrefix checkerInput.baseProgram finalProgram := by
      simpa [checkerInput, finalProof] using functionPrefix
    (fixture.registry.replayEquality checkerInput arena { index := 0 } edge
      finalProgram basePrefix []).isSome
  else
    false

-- Package replay rejects mutations of the actual retained theorem instance,
-- including its products, dynamic scope, origin, and recipe body.
#guard
  match semanticFixture? with
  | none => false
  | some fixture =>
      match fixture.session.state.engine.instanceHistory[0]?,
          fixture.session.arena.entries[0]? with
      | some event, some entry =>
          let wrongProducts := { event with products := [node 4, node 3] }
          let wrongScope :=
            { event with
              bindings :=
                [{ contractBinding with watches := [node 1] }]
              newBindings :=
                [{ contractBinding with watches := [node 1] }] }
          let wrongOrigin :=
            { event with origin := { event.origin with serial := event.origin.serial + 1 } }
          let wrongEntry := { entry with body := [0, 47] }
          let wrongArena :=
            { fixture.session.arena with
              entries := fixture.session.arena.entries.set! 0 wrongEntry }
          replaysInstanceEvent fixture fixture.session.arena event &&
            !replaysInstanceEvent fixture fixture.session.arena wrongProducts &&
            !replaysInstanceEvent fixture fixture.session.arena wrongScope &&
            !replaysInstanceEvent fixture fixture.session.arena wrongOrigin &&
            !replaysInstanceEvent fixture wrongArena event
      | _, _ => false

-- The equality theorem is tied to the actual endpoints and complete action,
-- not merely to a body which decodes under the right numeric schema.
#guard
  match semanticFixture? with
  | none => false
  | some fixture =>
      match fixture.session.state.engine.equalities[0]? with
      | some edge =>
          let wrongEndpoint := { edge with left := node 1 }
          let wrongOrigin :=
            { edge with origin := { edge.origin with effort := edge.origin.effort + 1 } }
          replaysEqualityEdge fixture fixture.session.arena edge &&
            !replaysEqualityEdge fixture fixture.session.arena wrongEndpoint &&
            !replaysEqualityEdge fixture fixture.session.arena wrongOrigin
      | none => false

def rejected? : Option (PolicySession.Session Rank) := do
  let .ok session := start rejectedPackage | none
  let (_, selection, viewed) <- invocation? session matcherKey
  match viewed.choose (.select selection) with
  | .invalidReply .malformedProposal stopped => some stopped
  | _ => none

-- A generically valid but package-invalid dynamic scope cannot cross the
-- session boundary.  Prospective payloads and matcher progress both roll back.
#guard
  match rejected? with
  | none => false
  | some session =>
      !session.live && !session.droppedWork && session.state.incomplete &&
        session.arena.entries.isEmpty && session.arena.bodyCells == 0 &&
        session.state.engine.programVersion == 0 &&
        session.state.engine.suggestions.isEmpty &&
        session.state.engine.bindings.isEmpty &&
        session.state.engine.equalities.isEmpty &&
        session.state.engine.metrics.matcherVisits == 0 &&
        session.state.engine.pending.isNone &&
        session.state.engine.pendingMatcher.isNone &&
        session.state.metrics.selectedInvocations == 1 &&
        (session.registry.packages[0]?).any fun package =>
          package.invocations == 1 &&
            match session.state.engine.matcherCursors[0]? with
            | some (some cursor) => cursor.offset == 0
            | _ => false

end Hex.Interval.PolicyFunctionConformance
