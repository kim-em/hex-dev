/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PolicySession
import HexInterval.Experiment.SemanticReplay
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arbitrary propagator end-to-end proof canary

A package recognizes `x * (1 - x)`, instantiates the opaque auxiliary function
`x ↦ 1/4 - (x - 1/2)^2`, admits the package-owned equality between those
expressions, propagates `[0, 1/4]` through the auxiliary node, and transports
that bound back to the original product.

The policy-session guard exercises compiled search and checks that it emitted
the quoted trace below.  The theorem at the end does not trust that search
run: ordinary kernel reduction replays the explicit trace through exact
fact/instance/equality schemas and produces a proof of the final real bound.
The generic engine and replay loop contain no branch for multiplication,
centering, real arithmetic, or these operation keys.
-/

namespace Hex.Interval.PropagatorE2EConformance

open Experiment Propagator PayloadArena PolicySession SemanticReplay

/-! ## Package-local expression language and fact domain -/

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "e2e.source" }
def oneKey : OpKey := { name := "e2e.one" }
def subKey : OpKey := { name := "e2e.sub" }
def mulKey : OpKey := { name := "e2e.mul" }
def centeredKey : OpKey := { name := "e2e.centered-product" }

def centeredForwardKey : RuleKey := { name := "e2e.centered.forward" }
def centeredInstantiateKey : RuleKey := { name := "e2e.centered.instantiate" }

def operations : Array Operation :=
  #[{ key := sourceKey, inputs := [], output := real },
    { key := oneKey, inputs := [], output := real },
    { key := subKey, inputs := [real, real], output := real },
    { key := mulKey, inputs := [real, real], output := real },
    { key := centeredKey, inputs := [real], output := real }]

def node (index : Nat) : NodeId := { index }

def instruction (operation : Nat) (args : List NodeId := []) : Node :=
  { domain := real, op := { index := operation }, args }

def baseProgram : Program :=
  { operations
    nodes :=
      #[instruction 0,
        instruction 1,
        instruction 2 [node 1, node 0],
        instruction 3 [node 0, node 2]] }

def extendedProgram : Program :=
  { baseProgram with
    nodes := baseProgram.nodes.push (instruction 4 [node 0]) }

inductive Fact where
  | top
  | unit
  | quarter
  | upperQuarter
  deriving DecidableEq, Repr

namespace Fact

def Allows : Fact -> ℝ -> Prop
  | .top, _ => True
  | .unit, value => 0 ≤ value ∧ value ≤ 1
  | .quarter, value => 0 ≤ value ∧ value ≤ (1 : ℝ) / 4
  | .upperQuarter, value => value ≤ (1 : ℝ) / 4

end Fact

def narrow : Fact -> Fact -> NarrowResult Fact
  | current, proposed =>
      if current == proposed then
        .noChange
      else
        match current, proposed with
        | .top, fact => .improved fact
        | _, .top => .noChange
        | .quarter, .upperQuarter => .noChange
        | .upperQuarter, .quarter => .improved .quarter
        | _, _ => .malformed 1

def searchDomain : Propagator.FactDomain Fact :=
  { top := fun _ => .top
    narrow := fun _ => narrow }

/-! ## Function-specific executable package -/

def centeredForward : Registration :=
  { key := centeredForwardKey
    head := centeredKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def centeredInstantiate : Registration :=
  { key := centeredInstantiateKey
    head := mulKey
    kind := .instantiate
    watches := []
    writes := []
    watchesProgram := true }

def factLabel : PayloadId := { index := 0 }
def instanceLabel : PayloadId := { index := 0 }
def equalityLabel : PayloadId := { index := 1 }

def taggedFormat (role : Role) (tag : Nat) : ReplayFormat :=
  { role
    schema := 0
    validateBody := fun body => body == [tag] }

def recognizesCentered (request : RuleRequest Fact) : Bool :=
  request.program.programVersion == request.action.programVersion &&
    request.program.operationKey? request.action.node == some mulKey &&
    match request.program.node? request.action.node with
    | some product =>
        product.args == [node 0, node 2] &&
          request.program.operationKey? (node 2) == some subKey &&
          match request.program.node? (node 2) with
          | some gap =>
              gap.args == [node 1, node 0] &&
                request.program.operationKey? (node 1) == some oneKey
          | none => false
    | none => false

def invokeInstantiate (request : RuleRequest Fact) : Plan Fact :=
  if recognizesCentered request then
    { outcome :=
        .success []
          [.instantiate
            { key := 1
              nodes :=
                [{ domain := real
                   op := { index := 4 }
                   args := [.existing (node 0)] }]
              equalities :=
                [{ left := .existing (node 3)
                   right := .proposed 0
                   payload := equalityLabel }]
              payload := instanceLabel }]
          { visitedEntries := 9, estimatedProofNodes := 1 }
      drafts :=
        [{ label := instanceLabel, role := .instance, schema := 0, body := [1] },
          { label := equalityLabel, role := .equality, schema := 0, body := [2] }] }
  else
    { outcome := .inapplicable, drafts := [] }

def invokeForward (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [{ node := input, fact := .unit, .. }], [target] =>
      if input == node 0 && target == node 4 then
        { outcome :=
            .success
              [{ node := target, fact := .quarter, payload := factLabel }]
              [] { arithmeticWork := 1, estimatedProofNodes := 1 }
          drafts :=
            [{ label := factLabel, role := .fact, schema := 0, body := [3] }] }
      else
        { outcome := .failed 2, drafts := [] }
  | _, _ => { outcome := .inapplicable, drafts := [] }

def runtimePackage : Propagator.Package Fact :=
  { Cache := Unit
    cache := ()
    operations
    handlers :=
      #[Handler.statelessPlanned centeredForward invokeForward
          #[taggedFormat .fact 3],
        Handler.statelessPlanned centeredInstantiate invokeInstantiate
          #[taggedFormat .instance 1, taggedFormat .equality 2]] }

def runtimePackages : Array (Propagator.Package Fact) := #[runtimePackage]

/-! ## Opaque search run and quoted trace -/

def endpointLimit : EndpointLimit :=
  { maxEndpointHeight := 8, maxAlignmentShift := 8 }

def engineLimits : Propagator.Limits :=
  { maxOperations := 5
    maxNodes := 5
    maxRules := 2
    maxRegistryEntries := 16
    maxReplayFormats := 3
    maxArity := 2
    maxApplications := 2
    maxQueueEntries := 16
    maxActions := 8
    maxAcceptedFacts := 4
    maxRetainedSuggestions := 2
    maxEffort := 0
    maxObservationValue := 16
    maxDiagnosticValue := 256
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 1
    maxProposalItems := 5
    maxInstances := 1
    maxGeneration := 1
    maxNodeDepth := 8
    maxEqualities := 1
    splitEndpointLimit := endpointLimit }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8
    maxTraversal := 256
    maxLiveOffers := 16 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 7
    maxBodyCells := 3
    maxDrafts := 7
    maxDraftCells := 3
    maxAtom := 3
    maxSchema := 0
    maxUses := 7 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def start? : Option (PolicySession.Session Fact) :=
  match PolicySession.Session.start searchDomain baseProgram runtimePackages
      #[.unit, .top, .top, .top] limits with
  | .ok session => some session
  | .error _ => none

inductive Command where
  | invoke (key : RuleKey)
  | instantiate
  | equality

def commandMatches : Command -> Propagator.Policy.OfferView -> Bool
  | .invoke key, { key := .invoke source, .. } => source.rule == key
  | .instantiate, { key := .instantiate source _, .. } =>
      source.rule == centeredInstantiateKey
  | .equality, { key := .equality _, .. } => true
  | _, _ => false

def selection? (session : PolicySession.Session Fact) (command : Command) :
    Option (Propagator.Policy.Selection × PolicySession.Session Fact) :=
  match session.view with
  | .ready view viewed =>
      match view.offers.toList.find? (commandMatches command) with
      | none => none
      | some offer =>
          some
            ({ scope := view.scope
               serial := view.serial
               programVersion := view.programVersion
               id := offer.id
               expected := offer.key },
             viewed)
  | .resource _ _ | .contradiction _ | .invalidSession _ => none

def execute? (session : PolicySession.Session Fact) (command : Command) :
    Option (PolicySession.Session Fact) := do
  let (selection, viewed) ← selection? session command
  match command, viewed.choose (.select selection) with
  | .invoke _, .rule _ _ next => some next
  | .instantiate, .instance _ (.instanceAdmitted [fresh]) next =>
      if fresh == node 4 then some next else none
  | .equality, .equality _ observation next =>
      if observation.outcome == .improved then some next else none
  | _, _ => none

def searchResult? : Option (PolicySession.Session Fact) := do
  let start ← start?
  let afterDiscovery ← execute? start (.invoke centeredInstantiateKey)
  let afterInstance ← execute? afterDiscovery .instantiate
  let afterForward ← execute? afterInstance (.invoke centeredForwardKey)
  execute? afterForward .equality

def instantiateAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 1 }
    key := centeredInstantiateKey
    node := node 3
    kind := .instantiate
    effort := 0
    inputs := [] }

def forwardAction : Action :=
  { serial := 1
    programVersion := 1
    application := { index := 1 }
    rule := { index := 0 }
    key := centeredForwardKey
    node := node 4
    kind := .forward
    effort := 0
    inputs := [{ node := node 0, version := 0 }] }

def instanceEvent : InstanceEvent :=
  { programVersion := 1
    origin := instantiateAction
    family := 1
    substitution := [node 3]
    products := [node 4]
    newNodes := [node 4]
    generation := 1
    equalities := [{ index := 0 }]
    payload := { index := 0 } }

def equalityEdge : EqualityEdge :=
  { left := node 3
    right := node 4
    generation := 1
    origin := instantiateAction
    payload := { index := 1 } }

def forwardEvent : FactEvent Fact :=
  { programVersion := 1
    node := node 4
    previous := { node := node 4, version := 0 }
    fact := .quarter
    version := 1
    cause := .rule forwardAction .quarter { index := 2 } }

def transportEvent : FactEvent Fact :=
  { programVersion := 1
    node := node 3
    previous := { node := node 3, version := 0 }
    fact := .quarter
    version := 1
    cause := .transport { index := 0 } { node := node 4, version := 1 } }

def instanceEntry : Entry :=
  { origin := instantiateAction, role := .instance, schema := 0, body := [1] }

def equalityEntry : Entry :=
  { origin := instantiateAction, role := .equality, schema := 0, body := [2] }

def factEntry : Entry :=
  { origin := forwardAction, role := .fact, schema := 0, body := [3] }

def quotedArena : Arena :=
  { entries := #[instanceEntry, equalityEntry, factEntry]
    bodyCells := 3 }

def quotedTrace : Trace Fact :=
  { program := extendedProgram
    programs := #[baseProgram, extendedProgram]
    instances := #[instanceEvent]
    equalities := #[equalityEdge]
    events := #[forwardEvent, transportEvent]
    arena := quotedArena }

def wrongRoleTrace : Trace Fact :=
  { quotedTrace with
    arena :=
      { entries :=
          #[instanceEntry, { equalityEntry with role := .fact }, factEntry]
        bodyCells := 3 } }

def wrongKeyTrace : Trace Fact :=
  { quotedTrace with
    arena :=
      { entries :=
          #[instanceEntry, { equalityEntry with schema := 1 }, factEntry]
        bodyCells := 3 } }

def wrongBodyTrace : Trace Fact :=
  { quotedTrace with
    arena :=
      { entries :=
          #[instanceEntry, equalityEntry, { factEntry with body := [2] }]
        bodyCells := 3 } }

def wrongInstanceBodyTrace : Trace Fact :=
  { quotedTrace with
    arena :=
      { entries :=
          #[{ instanceEntry with body := [2] }, equalityEntry, factEntry]
        bodyCells := 3 } }

def futureAction : Action :=
  { forwardAction with
    inputs := [{ node := node 4, version := 1 }] }

def futureEvent : FactEvent Fact :=
  { forwardEvent with
    cause := .rule futureAction .quarter { index := 2 } }

def futureTrace : Trace Fact :=
  { quotedTrace with
    events := #[futureEvent, transportEvent]
    arena :=
      { entries :=
          #[instanceEntry, equalityEntry, { factEntry with origin := futureAction }]
        bodyCells := 0 } }

def forgedMeetEvent : FactEvent Fact :=
  { forwardEvent with fact := .upperQuarter }

def forgedMeetTrace : Trace Fact :=
  { quotedTrace with events := #[forgedMeetEvent, transportEvent] }

-- Compiled search is only an untrusted trace producer.  This guard confirms
-- the current policy route emits the separately quoted certificate.
#guard
  match searchResult? with
  | none => false
  | some session =>
      session.state.engine.program == quotedTrace.program &&
        session.state.engine.instanceHistory == quotedTrace.instances &&
        session.state.engine.equalities == quotedTrace.equalities &&
        session.state.engine.history == quotedTrace.events &&
        session.arena == quotedTrace.arena

/-! ## Package-owned mathematical semantics -/

noncomputable section

def centeredValue (x : ℝ) : ℝ :=
  (1 : ℝ) / 4 - (x - (1 : ℝ) / 2) ^ 2

def BaseEquations (valuation : NodeId -> ℝ) : Prop :=
  valuation (node 1) = 1 ∧
    valuation (node 2) = valuation (node 1) - valuation (node 0) ∧
    valuation (node 3) = valuation (node 0) * valuation (node 2)

def ExtendedEquations (valuation : NodeId -> ℝ) : Prop :=
  BaseEquations valuation ∧
    valuation (node 4) = centeredValue (valuation (node 0))

def Models (program : Program) (valuation : NodeId -> ℝ) : Prop :=
  (program = baseProgram ∧ BaseEquations valuation) ∨
    (program = extendedProgram ∧ ExtendedEquations valuation)

def semantics : Semantics Fact :=
  { Value := ℝ
    models := Models
    holds := fun _ valuation fact => fact.fact.Allows (valuation fact.node)
    transport := by
      intro _ valuation left right fact equal holds
      change fact.Allows (valuation right)
      rw [← equal]
      exact holds }

theorem base_ne_extended : baseProgram ≠ extendedProgram := by
  decide

theorem modelsBase (valuation : NodeId -> ℝ) :
    Models baseProgram valuation -> BaseEquations valuation := by
  intro model
  rcases model with ⟨_, equations⟩ | ⟨equal, _⟩
  · exact equations
  · exact False.elim (base_ne_extended equal)

theorem modelsExtended (valuation : NodeId -> ℝ) :
    Models extendedProgram valuation -> ExtendedEquations valuation := by
  intro model
  rcases model with ⟨equal, _⟩ | ⟨_, equations⟩
  · exact False.elim (base_ne_extended equal.symm)
  · exact equations

theorem centeredExtends : semantics.Extends baseProgram extendedProgram := by
  intro valuation model
  let extended : NodeId -> ℝ :=
    fun current =>
      if current = node 4 then centeredValue (valuation (node 0))
      else valuation current
  refine ⟨extended, ?_, ?_⟩
  · right
    refine ⟨rfl, ?_⟩
    constructor
    · rcases modelsBase valuation model with ⟨one, gap, product⟩
      constructor
      · simpa [extended, node] using one
      constructor
      · simpa [extended, node] using gap
      · simpa [extended, node] using product
    · simp [extended, node]
  · intro current before
    have different : current ≠ node 4 := by
      intro equal
      subst current
      simp [baseProgram, node] at before
    simp [extended, different]

theorem centeredIdentity (valuation : NodeId -> ℝ)
    (equations : ExtendedEquations valuation) :
    valuation (node 3) = valuation (node 4) := by
  rcases equations with ⟨⟨one, gap, product⟩, centered⟩
  rw [product, gap, one, centered]
  simp only [centeredValue]
  ring

theorem centeredBounds (x : ℝ) (bounds : 0 ≤ x ∧ x ≤ 1) :
    Fact.quarter.Allows (centeredValue x) := by
  constructor
  · have product : 0 ≤ x * (1 - x) :=
      mul_nonneg bounds.1 (sub_nonneg.mpr bounds.2)
    have identity : centeredValue x = x * (1 - x) := by
      simp only [centeredValue]
      ring
    rw [identity]
    exact product
  · have square : 0 ≤ (x - (1 : ℝ) / 2) ^ 2 := sq_nonneg _
    simp only [centeredValue]
    linarith

theorem forwardEntails :
    semantics.Entails extendedProgram
      [{ node := node 0, fact := .unit }]
      { node := node 4, fact := .quarter } := by
  intro valuation model assumptions
  have input :=
    assumptions { node := node 0, fact := .unit } (List.Mem.head _)
  change Fact.unit.Allows (valuation (node 0)) at input
  change Fact.quarter.Allows (valuation (node 4))
  rw [(modelsExtended valuation model).2]
  exact centeredBounds _ input

inductive TaggedCertificate where
  | tagged

def decodeTag (expected : Nat) : List Nat -> Option TaggedCertificate
  | [actual] => if actual == expected then some .tagged else none
  | _ => none

def factSchema : PackedFactSchema semantics :=
  { rule := centeredForwardKey
    schema := 0
    Certificate := TaggedCertificate
    decode := decodeTag 3
    replay := fun _ action context _ =>
      if actionProof : action = forwardAction then
        if programProof : context.program = extendedProgram then
          if assumptionsProof :
              context.assumptions = [{ node := node 0, fact := .unit }] then
            if proposedProof :
                context.proposed = { node := node 4, fact := .quarter } then
              some
                { proof := by
                    rw [programProof, assumptionsProof, proposedProof]
                    exact forwardEntails }
            else none
          else none
        else none
      else none }

def instanceSchema : PackedInstanceSchema semantics :=
  { rule := centeredInstantiateKey
    schema := 0
    Certificate := TaggedCertificate
    decode := decodeTag 1
    replay := fun _ action context _ =>
      if actionProof : action = instantiateAction then
        if beforeProof : context.before = baseProgram then
          if afterProof : context.after = extendedProgram then
            if eventProof : context.event = instanceEvent then
              some
                { proof := by
                    rw [beforeProof, afterProof]
                    exact centeredExtends }
            else none
          else none
        else none
      else none }

def equalitySchema : PackedEqualitySchema semantics :=
  { rule := centeredInstantiateKey
    schema := 0
    Certificate := TaggedCertificate
    decode := decodeTag 2
    replay := fun _ action context _ =>
      if actionProof : action = instantiateAction then
        if programProof : context.program = extendedProgram then
          if edgeProof : context.edge = equalityEdge then
            some
              { proof := by
                  rw [programProof, edgeProof]
                  intro valuation model
                  exact centeredIdentity valuation (modelsExtended valuation model) }
          else none
        else none
      else none }

def semanticPackage : SemanticReplay.Package semantics :=
  { factSchemas := #[factSchema]
    instanceSchemas := #[instanceSchema]
    equalitySchemas := #[equalitySchema] }

def semanticPackages : Array (SemanticReplay.Package semantics) :=
  #[semanticPackage]

def meetEvidence (previous proposed installed : Fact) :
    Option (Evidence
      (∀ value : ℝ, installed.Allows value ↔
        previous.Allows value ∧ proposed.Allows value)) :=
  match previous, proposed, installed with
  | .top, fact, actual =>
      if equal : actual = fact then
        some
          { proof := by
              subst actual
              intro
              simp [Fact.Allows] }
      else none
  | fact, .top, actual =>
      if equal : actual = fact then
        some
          { proof := by
              subst actual
              intro
              simp [Fact.Allows] }
      else none
  | .quarter, .upperQuarter, .quarter =>
      some
        { proof := by
            intro
            simp only [Fact.Allows]
            constructor
            · intro bounds
              exact ⟨bounds, bounds.2⟩
            · intro bounds
              exact bounds.1 }
  | .upperQuarter, .quarter, .quarter =>
      some
        { proof := by
            intro
            simp only [Fact.Allows]
            constructor
            · intro bounds
              exact ⟨bounds.2, bounds⟩
            · intro bounds
              exact bounds.2 }
  | left, right, actual =>
      if same : left = right ∧ actual = left then
        some
          { proof := by
              rcases same with ⟨rfl, rfl⟩
              intro
              simp }
      else none

def proofDomain : FactDomainSchema semantics :=
  { top := fun _ => .top
    holdsPrefix := by
      intro _ _ valuation extended fact _ _ _ _ agreement
      change fact.fact.Allows (valuation fact.node) ↔
        fact.fact.Allows (extended fact.node)
      rw [agreement]
    topSound := by
      intro _ _ _ _ _ _
      trivial
    proveMeet := fun _ node previous proposed installed => do
      let evidence ← meetEvidence previous proposed installed
      pure
        { proof := by
            intro valuation _
            exact evidence.proof (valuation node) }
    proveImplies := fun _ node stronger requested =>
      match stronger, requested with
      | _, .top =>
          some
            { proof := by
                intro _ _ _
                trivial }
      | .quarter, .upperQuarter =>
          some
            { proof := by
                intro valuation _ stronger
                exact stronger.2 }
      | left, right =>
          if equal : left = right then
            some
              { proof := by
                  subst right
                  intro _ _ holds
                  exact holds }
          else none }

def checkerInput : CheckerInput Fact :=
  { baseProgram
    initialFacts := #[.unit, .top, .top, .top]
    target := { node := node 3, fact := .upperQuarter } }

def acceptsInputTrace (input : CheckerInput Fact) (trace : Trace Fact) : Bool :=
  match SemanticReplay.Registry.buildPackages runtimePackages semanticPackages with
  | .error _ => false
  | .ok registry =>
      (SemanticReplay.check registry proofDomain input trace).isSome

def acceptsTrace (trace : Trace Fact) : Bool :=
  acceptsInputTrace checkerInput trace

def generatedTargetInput : CheckerInput Fact :=
  { checkerInput with target := { node := node 4, fact := .quarter } }

def checked? :
    Option (Evidence
      (semantics.Entails baseProgram
        (initialContext checkerInput) checkerInput.target)) :=
  match SemanticReplay.Registry.buildPackages runtimePackages semanticPackages with
  | .error _ => none
  | .ok registry =>
      SemanticReplay.check registry proofDomain checkerInput quotedTrace

theorem checked_isSome : checked?.isSome = true := by
  decide +kernel

theorem rejects_wrong_role : acceptsTrace wrongRoleTrace = false := by
  decide +kernel

theorem rejects_wrong_key : acceptsTrace wrongKeyTrace = false := by
  decide +kernel

theorem rejects_wrong_body : acceptsTrace wrongBodyTrace = false := by
  decide +kernel

theorem rejects_wrong_instance_body :
    acceptsTrace wrongInstanceBodyTrace = false := by
  decide +kernel

theorem rejects_future_reference : acceptsTrace futureTrace = false := by
  decide +kernel

theorem rejects_forged_meet : acceptsTrace forgedMeetTrace = false := by
  decide +kernel

theorem rejects_generated_target :
    acceptsInputTrace generatedTargetInput quotedTrace = false := by
  decide +kernel

/-- The kernel checker itself composes the package-owned conservative
extension proof and returns a theorem about the caller's original graph. -/
theorem product_le_quarter :
    semantics.Entails baseProgram
      (initialContext checkerInput) checkerInput.target := by
  match result : checked? with
  | some evidence => exact evidence.proof
  | none =>
      have accepted := checked_isSome
      simp [result] at accepted

/-- Compatibility name emphasizing that no generated node occurs in the
theorem returned by the generic checker. -/
theorem base_product_le_quarter :
    semantics.Entails baseProgram
      (initialContext checkerInput) checkerInput.target :=
  product_le_quarter

/-- A concrete valuation of the caller's four-node expression graph.  This
turns the structural replay theorem into the ordinary inequality a tactic user
would see and demonstrates that the checked model context is inhabited. -/
def baseValuation (x : ℝ) : NodeId -> ℝ :=
  fun current =>
    if current = node 0 then x
    else if current = node 1 then 1
    else if current = node 2 then 1 - x
    else if current = node 3 then x * (1 - x)
    else 0

theorem baseValuation_models (x : ℝ) :
    Models baseProgram (baseValuation x) := by
  left
  refine ⟨rfl, ?_⟩
  simp [BaseEquations, baseValuation, node]

/-- Human-facing consequence of the arbitrary-propagator trace.  The proof
calls the theorem returned by the generic checker; it does not invoke a
separate arithmetic tactic to establish the upper bound. -/
theorem product_le_quarter_raw (x : ℝ) (lower : 0 ≤ x) (upper : x ≤ 1) :
    x * (1 - x) ≤ (1 : ℝ) / 4 := by
  have initial :
      ∀ assumption, assumption ∈ initialContext checkerInput ->
        semantics.holds baseProgram (baseValuation x) assumption := by
    intro assumption member
    simp [initialContext, initialContextFrom, checkerInput] at member
    rcases member with equal | equal | equal | equal
    · subst assumption
      exact ⟨lower, upper⟩
    all_goals subst assumption
    all_goals trivial
  have result :=
    product_le_quarter (baseValuation x) (baseValuation_models x) initial
  change Fact.upperQuarter.Allows (baseValuation x (node 3)) at result
  simpa [Fact.Allows, baseValuation, node] using result

end

end Hex.Interval.PropagatorE2EConformance
