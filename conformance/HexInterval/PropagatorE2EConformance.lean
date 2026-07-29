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

noncomputable section

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

def emptyFormat (role : Role) : ReplayFormat :=
  { role
    schema := 0
    validateBody := fun body => body.isEmpty }

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
              triggers := [node 3, node 0, node 2, node 1]
              claimedGeneration := 1
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
        [{ label := instanceLabel, role := .instance, schema := 0, body := [] },
          { label := equalityLabel, role := .equality, schema := 0, body := [] }] }
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
            [{ label := factLabel, role := .fact, schema := 0, body := [] }] }
      else
        { outcome := .failed 2, drafts := [] }
  | _, _ => { outcome := .inapplicable, drafts := [] }

def runtimePackage : Propagator.Package Fact :=
  { Cache := Unit
    cache := ()
    operations
    handlers :=
      #[Handler.statelessPlanned centeredForward invokeForward
          #[emptyFormat .fact],
        Handler.statelessPlanned centeredInstantiate invokeInstantiate
          #[emptyFormat .instance, emptyFormat .equality]] }

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
    maxDiagnosticValue := 16
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 1
    maxProposalItems := 5
    maxInstances := 1
    maxGeneration := 1
    maxEqualities := 1
    splitEndpointLimit := endpointLimit }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8
    maxTraversal := 256
    maxLiveOffers := 16 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 3
    maxBodyCells := 0
    maxAtom := 0
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
  { origin := instantiateAction, role := .instance, schema := 0, body := [] }

def equalityEntry : Entry :=
  { origin := instantiateAction, role := .equality, schema := 0, body := [] }

def factEntry : Entry :=
  { origin := forwardAction, role := .fact, schema := 0, body := [] }

def quotedArena : Arena :=
  { entries := #[instanceEntry, equalityEntry, factEntry]
    bodyCells := 0 }

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
        bodyCells := 0 } }

def wrongKeyTrace : Trace Fact :=
  { quotedTrace with
    arena :=
      { entries :=
          #[instanceEntry, { equalityEntry with schema := 1 }, factEntry]
        bodyCells := 0 } }

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

inductive UnitCertificate where
  | unit

def decodeUnit : List Nat -> Option UnitCertificate
  | [] => some .unit
  | _ :: _ => none

def factSchema : PackedFactSchema semantics :=
  { rule := centeredForwardKey
    schema := 0
    Certificate := UnitCertificate
    decode := decodeUnit
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
    Certificate := UnitCertificate
    decode := decodeUnit
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
    Certificate := UnitCertificate
    decode := decodeUnit
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

def acceptsTrace (trace : Trace Fact) : Bool :=
  match SemanticReplay.Registry.buildPackages runtimePackages semanticPackages with
  | .error _ => false
  | .ok registry =>
      (SemanticReplay.check registry proofDomain checkerInput trace).isSome

def checked? :
    Option (Evidence
      (semantics.Entails extendedProgram
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

theorem rejects_future_reference : acceptsTrace futureTrace = false := by
  decide +kernel

theorem rejects_forged_meet : acceptsTrace forgedMeetTrace = false := by
  decide +kernel

/-- The kernel-checked result: for every real valuation satisfying the quoted
expression program, `0 ≤ x ≤ 1` implies `x * (1 - x) ≤ 1/4`. -/
theorem product_le_quarter :
    semantics.Entails extendedProgram
      (initialContext checkerInput) checkerInput.target := by
  match result : checked? with
  | some evidence => exact evidence.proof
  | none =>
      have accepted := checked_isSome
      simp [result] at accepted

/-- The checked extension is conservative, so the result also applies to
every valuation of the original four-node program. -/
theorem base_product_le_quarter :
    semantics.Entails baseProgram
      (initialContext checkerInput) checkerInput.target := by
  intro valuation model initial
  obtain ⟨extended, extendedModel, agreement⟩ :=
    centeredExtends valuation model
  have extendedInitial :
      ∀ assumption, assumption ∈ initialContext checkerInput ->
        semantics.holds extendedProgram extended assumption := by
    intro assumption member
    have before : assumption.node.index < baseProgram.nodes.size := by
      have listed := member
      simp [initialContext, initialContextFrom, checkerInput] at listed
      rcases listed with equal | equal | equal | equal
      all_goals subst assumption
      all_goals decide
    have holds := initial assumption member
    have equal := agreement assumption.node before
    change assumption.fact.Allows (valuation assumption.node) at holds
    change assumption.fact.Allows (extended assumption.node)
    rw [equal]
    exact holds
  have result :=
    product_le_quarter extended extendedModel extendedInitial
  have equal := agreement (node 3) (by decide)
  change Fact.upperQuarter.Allows (extended (node 3)) at result
  change Fact.upperQuarter.Allows (valuation (node 3))
  rw [equal] at result
  exact result

end

end Hex.Interval.PropagatorE2EConformance
