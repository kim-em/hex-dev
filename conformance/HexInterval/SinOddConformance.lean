/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PolicySession
import HexInterval.Experiment.SemanticReplay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Non-polynomial arbitrary-propagator proof canary

An opaque package recognizes `sin (-x)`, instantiates `sin x` and `-(sin x)`,
and admits their equality using `Real.sin_neg`. Independent sine and negation
propagators then prove the auxiliary interval before generic equality
transport narrows the original expression.

The compiled policy session below is only an untrusted trace producer. The
public theorem is obtained by transparent replay of the quoted trace through
package-owned fact, instance, and equality schemas.
-/

namespace Hex.Interval.SinOddConformance

open Experiment Propagator PayloadArena PolicySession SemanticReplay

noncomputable section

/-! ## Package-local expression language and fact domain -/

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "sin-odd.source" }
def negKey : OpKey := { name := "sin-odd.neg" }
def sinKey : OpKey := { name := "sin-odd.sin" }

def sinForwardKey : RuleKey := { name := "sin-odd.sin.forward" }
def negForwardKey : RuleKey := { name := "sin-odd.neg.forward" }
def sinNegInstantiateKey : RuleKey := { name := "sin-odd.instantiate" }

def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

def negOperation : Operation :=
  { key := negKey, inputs := [real], output := real }

def sinOperation : Operation :=
  { key := sinKey, inputs := [real], output := real }

def operations : Array Operation :=
  #[sourceOperation, negOperation, sinOperation]

def node (index : Nat) : NodeId := { index }

def instruction (operation : Nat) (args : List NodeId := []) : Node :=
  { domain := real, op := { index := operation }, args }

def baseProgram : Program :=
  { operations
    nodes :=
      #[instruction 0,
        instruction 1 [node 0],
        instruction 2 [node 1]] }

def extendedProgram : Program :=
  { baseProgram with
    nodes :=
      baseProgram.nodes ++
        #[instruction 2 [node 0],
          instruction 1 [node 3]] }

inductive Fact where
  | top
  | zeroTwo
  | zeroOne
  | negOneZero
  deriving DecidableEq, Repr

namespace Fact

def Allows : Fact -> ℝ -> Prop
  | .top, _ => True
  | .zeroTwo, value => 0 ≤ value ∧ value ≤ 2
  | .zeroOne, value => 0 ≤ value ∧ value ≤ 1
  | .negOneZero, value => -1 ≤ value ∧ value ≤ 0

end Fact

def narrow : Fact -> Fact -> NarrowResult Fact
  | current, proposed =>
      if current == proposed then
        .noChange
      else
        match current, proposed with
        | .top, fact => .improved fact
        | _, .top => .noChange
        | _, _ => .malformed 1

def searchDomain : Propagator.FactDomain Fact :=
  { top := fun _ => .top
    narrow := fun _ => narrow }

/-! ## Function-specific executable package -/

def sinForward : Registration :=
  { key := sinForwardKey
    head := sinKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def negForward : Registration :=
  { key := negForwardKey
    head := negKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def sinNegInstantiate : Registration :=
  { key := sinNegInstantiateKey
    head := sinKey
    kind := .instantiate
    watches := []
    writes := [] }

def factLabel : PayloadId := { index := 0 }
def instanceLabel : PayloadId := { index := 0 }
def equalityLabel : PayloadId := { index := 1 }

def unaryFactFormat : ReplayFormat :=
  { role := .fact
    schema := 0
    validateBody := fun body =>
      match body with
      | [_, _, 0] => true
      | _ => false }

def taggedFormat (role : Role) (tag : Nat) : ReplayFormat :=
  { role
    schema := 0
    validateBody := fun body => body == [tag] }

structure SinNegBinding where
  input : NodeId
  negative : NodeId

def sinNegBinding? (request : RuleRequest Fact) : Option SinNegBinding := do
  if request.program.programVersion != request.action.programVersion then none
  else pure ()
  if request.program.operationKey? request.action.node != some sinKey then none
  else pure ()
  let outer ← request.program.node? request.action.node
  let [negative] := outer.args | none
  if request.program.operationKey? negative != some negKey then none else pure ()
  let negation ← request.program.node? negative
  let [input] := negation.args | none
  pure { input, negative }

def invokeInstantiate (request : RuleRequest Fact) : Plan Fact :=
  match sinNegBinding? request with
  | none => { outcome := .inapplicable, drafts := [] }
  | some binding =>
      { outcome :=
          .success []
            [.instantiate
              { key := 1
                triggers := [request.action.node, binding.negative, binding.input]
                claimedGeneration := 1
                nodes :=
                  [{ domain := real
                     op := { index := 2 }
                     args := [.existing binding.input] },
                   { domain := real
                     op := { index := 1 }
                     args := [.proposed 0] }]
                equalities :=
                  [{ left := .existing request.action.node
                     right := .proposed 1
                     payload := equalityLabel }]
                payload := instanceLabel }]
            { visitedEntries := 8, estimatedProofNodes := 1 }
        drafts :=
          [{ label := instanceLabel, role := .instance, schema := 0, body := [0] },
            { label := equalityLabel, role := .equality, schema := 0, body := [1] }] }

def invokeSinForward (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [{ node := input, fact := .zeroTwo, .. }], [target] =>
      { outcome :=
          .success
            [{ node := target, fact := .zeroOne, payload := factLabel }]
            [] { arithmeticWork := 1, estimatedProofNodes := 1 }
        drafts :=
          [{ label := factLabel
             role := .fact
             schema := 0
             body := [input.index, target.index, 0] }] }
  | _, _ => { outcome := .inapplicable, drafts := [] }

def invokeNegForward (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [{ node := input, fact := .zeroOne, .. }], [target] =>
      { outcome :=
          .success
            [{ node := target, fact := .negOneZero, payload := factLabel }]
            [] { arithmeticWork := 1, estimatedProofNodes := 1 }
        drafts :=
          [{ label := factLabel
             role := .fact
             schema := 0
             body := [input.index, target.index, 0] }] }
  | _, _ => { outcome := .inapplicable, drafts := [] }

def runtimePackage : Propagator.Package Fact :=
  { Cache := Unit
    cache := ()
    operations
    handlers :=
      #[Handler.statelessPlanned sinForward invokeSinForward
          #[unaryFactFormat],
        Handler.statelessPlanned negForward invokeNegForward
          #[unaryFactFormat],
        Handler.statelessPlanned sinNegInstantiate invokeInstantiate
          #[taggedFormat .instance 0, taggedFormat .equality 1]] }

def runtimePackages : Array (Propagator.Package Fact) := #[runtimePackage]

/-! ## Opaque search run and quoted trace -/

def endpointLimit : EndpointLimit :=
  { maxEndpointHeight := 8, maxAlignmentShift := 8 }

def engineLimits : Propagator.Limits :=
  { maxOperations := 3
    maxNodes := 5
    maxRules := 3
    maxRegistryEntries := 16
    maxReplayFormats := 4
    maxArity := 1
    maxApplications := 6
    maxQueueEntries := 24
    maxActions := 12
    maxAcceptedFacts := 6
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
  { maxDecisions := 12
    maxTraversal := 512
    maxLiveOffers := 24 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4
    maxBodyCells := 8
    maxAtom := 4
    maxSchema := 0
    maxUses := 7 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def start? : Option (PolicySession.Session Fact) :=
  match PolicySession.Session.start searchDomain baseProgram runtimePackages
      #[.zeroTwo, .top, .top] limits with
  | .ok session => some session
  | .error _ => none

inductive Command where
  | invoke (key : RuleKey) (target : NodeId)
  | instantiate
  | equality

def commandMatches : Command -> Propagator.Policy.OfferView -> Bool
  | .invoke key target, { key := .invoke source, .. } =>
      source.rule == key && source.anchor == target
  | .instantiate, { key := .instantiate source _, .. } =>
      source.rule == sinNegInstantiateKey
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
  | .invoke _ _, .rule _ _ next => some next
  | .instantiate, .instance _ (.instanceAdmitted fresh) next =>
      if fresh == [node 3, node 4] then some next else none
  | .equality, .equality _ observation next =>
      if observation.outcome == .improved then some next else none
  | _, _ => none

def searchResult? : Option (PolicySession.Session Fact) := do
  let start ← start?
  let afterDiscovery ←
    execute? start (.invoke sinNegInstantiateKey (node 2))
  let afterInstance ← execute? afterDiscovery .instantiate
  let afterSin ← execute? afterInstance (.invoke sinForwardKey (node 3))
  let afterNeg ← execute? afterSin (.invoke negForwardKey (node 4))
  execute? afterNeg .equality

def instantiateAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 2 }
    rule := { index := 2 }
    key := sinNegInstantiateKey
    node := node 2
    kind := .instantiate
    effort := 0
    inputs := [] }

def sinAction : Action :=
  { serial := 1
    programVersion := 1
    application := { index := 3 }
    rule := { index := 0 }
    key := sinForwardKey
    node := node 3
    kind := .forward
    effort := 0
    inputs := [{ node := node 0, version := 0 }] }

def negAction : Action :=
  { serial := 2
    programVersion := 1
    application := { index := 5 }
    rule := { index := 1 }
    key := negForwardKey
    node := node 4
    kind := .forward
    effort := 0
    inputs := [{ node := node 3, version := 1 }] }

def instanceEvent : InstanceEvent :=
  { programVersion := 1
    origin := instantiateAction
    family := 1
    substitution := [node 2]
    products := [node 3, node 4]
    newNodes := [node 3, node 4]
    generation := 1
    equalities := [{ index := 0 }]
    payload := { index := 0 } }

def equalityEdge : EqualityEdge :=
  { left := node 2
    right := node 4
    generation := 1
    origin := instantiateAction
    payload := { index := 1 } }

def sinEvent : FactEvent Fact :=
  { programVersion := 1
    node := node 3
    previous := { node := node 3, version := 0 }
    fact := .zeroOne
    version := 1
    cause := .rule sinAction .zeroOne { index := 2 } }

def negEvent : FactEvent Fact :=
  { programVersion := 1
    node := node 4
    previous := { node := node 4, version := 0 }
    fact := .negOneZero
    version := 1
    cause := .rule negAction .negOneZero { index := 3 } }

def transportEvent : FactEvent Fact :=
  { programVersion := 1
    node := node 2
    previous := { node := node 2, version := 0 }
    fact := .negOneZero
    version := 1
    cause := .transport { index := 0 } { node := node 4, version := 1 } }

def instanceEntry : Entry :=
  { origin := instantiateAction, role := .instance, schema := 0, body := [0] }

def equalityEntry : Entry :=
  { origin := instantiateAction, role := .equality, schema := 0, body := [1] }

def sinEntry : Entry :=
  { origin := sinAction, role := .fact, schema := 0, body := [0, 3, 0] }

def negEntry : Entry :=
  { origin := negAction, role := .fact, schema := 0, body := [3, 4, 0] }

def quotedArena : Arena :=
  { entries := #[instanceEntry, equalityEntry, sinEntry, negEntry]
    bodyCells := 8 }

def quotedTrace : Trace Fact :=
  { program := extendedProgram
    programs := #[baseProgram, extendedProgram]
    instances := #[instanceEvent]
    equalities := #[equalityEdge]
    events := #[sinEvent, negEvent, transportEvent]
    arena := quotedArena }

/-- A trace cannot silently replace the package-owned sine-oddness identity
schema with a different local recipe version. -/
def wrongSinIdentitySchemaTrace : Trace Fact :=
  { quotedTrace with
    arena :=
      { entries :=
          #[instanceEntry, { equalityEntry with schema := 1 }, sinEntry, negEntry]
        bodyCells := 8 } }

/-- The identity schema also rejects a body carrying the instance method tag
instead of the `Real.sin_neg` method tag. -/
def wrongSinIdentityMethodTrace : Trace Fact :=
  { quotedTrace with
    arena :=
      { entries :=
          #[instanceEntry, { equalityEntry with body := [0] }, sinEntry, negEntry]
        bodyCells := 8 } }

-- This compiled guard checks only that the current untrusted search route
-- emits the separately quoted certificate.
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

/-- Structural meaning of one node. The package interprets only its own
opaque operation keys; nodes owned by other packages remain unconstrained. -/
def NodeMeaning (program : Program) (valuation : NodeId -> ℝ)
    (output : NodeId) (instruction : Node) : Prop :=
  match program.operation? instruction.op with
  | none => False
  | some operation =>
      if operation.key = negKey then
        match instruction.args with
        | [input] => valuation output = -valuation input
        | _ => False
      else if operation.key = sinKey then
        match instruction.args with
        | [input] => valuation output = Real.sin (valuation input)
        | _ => False
      else
        True

/-- Whole-program structural semantics. This is not a lookup table for the
two programs used by the canary. -/
def Models (program : Program) (valuation : NodeId -> ℝ) : Prop :=
  ∀ output instruction, program.node? output = some instruction ->
    NodeMeaning program valuation output instruction

/-- A checked structural assertion that `output` applies one unary operation
to `input`. -/
structure UnaryShape (program : Program) (key : OpKey)
    (output input : NodeId) where
  instruction : Node
  operation : Operation
  nodeProof : program.node? output = some instruction
  operationProof : program.operation? instruction.op = some operation
  keyProof : operation.key = key
  argsProof : instruction.args = [input]

/-- Transparently recover a unary node shape from an untrusted program. -/
def checkUnary? (program : Program) (key : OpKey)
    (output input : NodeId) :
    Option (UnaryShape program key output input) :=
  match nodeProof : program.node? output with
  | none => none
  | some instruction =>
      if argsProof : instruction.args = [input] then
        match operationProof : program.operation? instruction.op with
        | none => none
        | some operation =>
            if keyProof : operation.key = key then
              some
                { instruction
                  operation
                  nodeProof
                  operationProof
                  keyProof
                  argsProof }
            else none
      else none

/-- A unary node together with the input recovered from its checked shape. -/
structure UnaryWitness (program : Program) (key : OpKey) (output : NodeId) where
  input : NodeId
  shape : UnaryShape program key output input

def unaryWitness? (program : Program) (key : OpKey) (output : NodeId) :
    Option (UnaryWitness program key output) := do
  let instruction ← program.node? output
  let [input] := instruction.args | none
  let shape ← checkUnary? program key output input
  pure { input, shape }

theorem UnaryShape.negValue
    (shape : UnaryShape program negKey output input)
    (model : Models program valuation) :
    valuation output = -valuation input := by
  have meaning := model output shape.instruction shape.nodeProof
  simp [NodeMeaning, shape.operationProof, shape.keyProof, shape.argsProof,
    negKey] at meaning
  exact meaning

theorem UnaryShape.sinValue
    (shape : UnaryShape program sinKey output input)
    (model : Models program valuation) :
    valuation output = Real.sin (valuation input) := by
  have meaning := model output shape.instruction shape.nodeProof
  simp [NodeMeaning, shape.operationProof, shape.keyProof, shape.argsProof,
    negKey, sinKey] at meaning
  exact meaning

/-- The four structural unary applications which make a `sin (-x)` node
equal to the instantiated `-(sin x)` node. -/
structure SinNegWitness (program : Program) (left right : NodeId) where
  negative : NodeId
  input : NodeId
  positive : NodeId
  leftSin : UnaryShape program sinKey left negative
  inputNeg : UnaryShape program negKey negative input
  rightNeg : UnaryShape program negKey right positive
  positiveSin : UnaryShape program sinKey positive input

def sinNegWitness? (program : Program) (left right : NodeId) :
    Option (SinNegWitness program left right) := do
  let leftSin ← unaryWitness? program sinKey left
  let inputNeg ← unaryWitness? program negKey leftSin.input
  let rightNeg ← unaryWitness? program negKey right
  let positiveSin ← unaryWitness? program sinKey rightNeg.input
  if same : positiveSin.input = inputNeg.input then
    pure
      { negative := leftSin.input
        input := inputNeg.input
        positive := rightNeg.input
        leftSin := leftSin.shape
        inputNeg := inputNeg.shape
        rightNeg := rightNeg.shape
        positiveSin := by simpa [same] using positiveSin.shape }
  else
    none

def semantics : Semantics Fact :=
  { Value := ℝ
    models := Models
    holds := fun _ valuation fact => fact.fact.Allows (valuation fact.node)
    transport := by
      intro _ valuation left right fact equal holds
      change fact.Allows (valuation right)
      rw [← equal]
      exact holds }

def baseNegativeShape :
    UnaryShape baseProgram negKey (node 1) (node 0) :=
  { instruction := instruction 1 [node 0]
    operation := negOperation
    nodeProof := by decide
    operationProof := by decide
    keyProof := by decide
    argsProof := rfl }

def baseSinShape :
    UnaryShape baseProgram sinKey (node 2) (node 1) :=
  { instruction := instruction 2 [node 1]
    operation := sinOperation
    nodeProof := by decide
    operationProof := by decide
    keyProof := by decide
    argsProof := rfl }

def extendedNegativeShape :
    UnaryShape extendedProgram negKey (node 1) (node 0) :=
  { instruction := instruction 1 [node 0]
    operation := negOperation
    nodeProof := by decide
    operationProof := by decide
    keyProof := by decide
    argsProof := rfl }

def extendedOriginalSinShape :
    UnaryShape extendedProgram sinKey (node 2) (node 1) :=
  { instruction := instruction 2 [node 1]
    operation := sinOperation
    nodeProof := by decide
    operationProof := by decide
    keyProof := by decide
    argsProof := rfl }

def extendedPositiveSinShape :
    UnaryShape extendedProgram sinKey (node 3) (node 0) :=
  { instruction := instruction 2 [node 0]
    operation := sinOperation
    nodeProof := by decide
    operationProof := by decide
    keyProof := by decide
    argsProof := rfl }

def extendedAuxNegShape :
    UnaryShape extendedProgram negKey (node 4) (node 3) :=
  { instruction := instruction 1 [node 3]
    operation := negOperation
    nodeProof := by decide
    operationProof := by decide
    keyProof := by decide
    argsProof := rfl }

theorem sinNegExtends : semantics.Extends baseProgram extendedProgram := by
  intro valuation model
  have negative := baseNegativeShape.negValue model
  have original := baseSinShape.sinValue model
  let extended : NodeId -> ℝ :=
    fun current =>
      if current = node 3 then Real.sin (valuation (node 0))
      else if current = node 4 then -Real.sin (valuation (node 0))
      else valuation current
  refine ⟨extended, ?_, ?_⟩
  · intro output current lookup
    rcases output with ⟨index⟩
    change extendedProgram.nodes[index]? = some current at lookup
    obtain ⟨bound, currentEq⟩ := Array.getElem?_eq_some_iff.mp lookup
    change index < 5 at bound
    interval_cases index
    all_goals
      simp [extendedProgram, baseProgram, instruction] at currentEq
      subst current
      simp [NodeMeaning, Program.operation?, extendedProgram, baseProgram,
        operations, sourceOperation, negOperation, sinOperation, instruction,
        extended, node, sourceKey, negKey, sinKey]
      try simpa [node] using negative
      try simpa [node] using original
  · intro current before
    have notThree : current ≠ node 3 := by
      intro equal
      subst current
      simp [baseProgram, node] at before
    have notFour : current ≠ node 4 := by
      intro equal
      subst current
      simp [baseProgram, node] at before
    simp [extended, notThree, notFour]

theorem sinNegIdentity
    (witness : SinNegWitness program left right) :
    semantics.Equivalent program left right := by
  change ∀ valuation : NodeId -> ℝ, Models program valuation ->
    valuation left = valuation right
  intro valuation model
  calc
    valuation left = Real.sin (valuation witness.negative) :=
      witness.leftSin.sinValue model
    _ = Real.sin (-valuation witness.input) := by
      rw [witness.inputNeg.negValue model]
    _ = -Real.sin (valuation witness.input) := Real.sin_neg _
    _ = -valuation witness.positive := by
      rw [witness.positiveSin.sinValue model]
    _ = valuation right := (witness.rightNeg.negValue model).symm

theorem sinBounds (x : ℝ) (bounds : 0 ≤ x ∧ x ≤ 2) :
    Fact.zeroOne.Allows (Real.sin x) := by
  constructor
  · exact Real.sin_nonneg_of_nonneg_of_le_pi bounds.1
      (bounds.2.trans Real.two_le_pi)
  · exact Real.sin_le_one x

theorem negBounds (x : ℝ) (bounds : Fact.zeroOne.Allows x) :
    Fact.negOneZero.Allows (-x) := by
  constructor <;> linarith [bounds.1, bounds.2]

theorem sinEntails
    (shape : UnaryShape program sinKey target input) :
    semantics.Entails program
      [{ node := input, fact := .zeroTwo }]
      { node := target, fact := .zeroOne } := by
  intro valuation model assumptions
  have inputBounds :=
    assumptions { node := input, fact := .zeroTwo } (List.Mem.head _)
  change Fact.zeroTwo.Allows (valuation input) at inputBounds
  change Fact.zeroOne.Allows (valuation target)
  rw [shape.sinValue model]
  exact sinBounds _ inputBounds

theorem negEntails
    (shape : UnaryShape program negKey target input) :
    semantics.Entails program
      [{ node := input, fact := .zeroOne }]
      { node := target, fact := .negOneZero } := by
  intro valuation model assumptions
  have inputBounds :=
    assumptions { node := input, fact := .zeroOne } (List.Mem.head _)
  change Fact.zeroOne.Allows (valuation input) at inputBounds
  change Fact.negOneZero.Allows (valuation target)
  rw [shape.negValue model]
  exact negBounds _ inputBounds

structure UnaryCertificate where
  input : Nat
  target : Nat

def decodeUnary : List Nat -> Option UnaryCertificate
  | [input, target, 0] => some { input, target }
  | _ => none

inductive InstanceCertificate where
  | appendSinNeg

def decodeInstance : List Nat -> Option InstanceCertificate
  | [0] => some .appendSinNeg
  | _ => none

inductive IdentityCertificate where
  | sinNeg

def decodeIdentity : List Nat -> Option IdentityCertificate
  | [1] => some .sinNeg
  | _ => none

def sinFactSchema : PackedFactSchema semantics :=
  { rule := sinForwardKey
    schema := 0
    Certificate := UnaryCertificate
    decode := decodeUnary
    replay := fun _ action context certificate => do
      if action.key != sinForwardKey || action.kind != .forward then none
      else pure ()
      let input := node certificate.input
      let target := node certificate.target
      if action.node != target then none else pure ()
      let shape ← checkUnary? context.program sinKey target input
      if assumptionsProof :
          context.assumptions = [{ node := input, fact := .zeroTwo }] then
        if proposedProof :
            context.proposed = { node := target, fact := .zeroOne } then
          some
            { proof := by
                rw [assumptionsProof, proposedProof]
                exact sinEntails shape }
        else none
      else none }

def negFactSchema : PackedFactSchema semantics :=
  { rule := negForwardKey
    schema := 0
    Certificate := UnaryCertificate
    decode := decodeUnary
    replay := fun _ action context certificate => do
      if action.key != negForwardKey || action.kind != .forward then none
      else pure ()
      let input := node certificate.input
      let target := node certificate.target
      if action.node != target then none else pure ()
      let shape ← checkUnary? context.program negKey target input
      if assumptionsProof :
          context.assumptions = [{ node := input, fact := .zeroOne }] then
        if proposedProof :
            context.proposed = { node := target, fact := .negOneZero } then
          some
            { proof := by
                rw [assumptionsProof, proposedProof]
                exact negEntails shape }
        else none
      else none }

def instanceSchema : PackedInstanceSchema semantics :=
  { rule := sinNegInstantiateKey
    schema := 0
    Certificate := InstanceCertificate
    decode := decodeInstance
    replay := fun _ action context _ =>
      if action.key != sinNegInstantiateKey ||
          action.kind != .instantiate then none
      else if beforeProof : context.before = baseProgram then
        if afterProof : context.after = extendedProgram then
          if context.event.products != [node 3, node 4] ||
              context.event.newNodes != [node 3, node 4] ||
              context.event.substitution != [node 2] then none
          else
            some
              { proof := by
                  rw [beforeProof, afterProof]
                  exact sinNegExtends }
        else none
      else none }

def equalitySchema : PackedEqualitySchema semantics :=
  { rule := sinNegInstantiateKey
    schema := 0
    Certificate := IdentityCertificate
    decode := decodeIdentity
    replay := fun _ action context _ => do
      if action.key != sinNegInstantiateKey ||
          action.kind != .instantiate then none
      else pure ()
      let witness ←
        sinNegWitness? context.program context.edge.left context.edge.right
      some { proof := sinNegIdentity witness } }

def semanticPackage : SemanticReplay.Package semantics :=
  { factSchemas := #[sinFactSchema, negFactSchema]
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
    proveImplies := fun _ _ stronger requested =>
      if equal : stronger = requested then
        some
          { proof := by
              subst requested
              intro _ _ holds
              exact holds }
      else if top : requested = .top then
        some
          { proof := by
              subst requested
              intro _ _ _
              trivial }
      else none }

def checkerInput : CheckerInput Fact :=
  { baseProgram
    initialFacts := #[.zeroTwo, .top, .top]
    target := { node := node 2, fact := .negOneZero } }

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

theorem rejects_wrong_sin_identity_schema :
    acceptsTrace wrongSinIdentitySchemaTrace = false := by
  decide +kernel

theorem rejects_wrong_sin_identity_method :
    acceptsTrace wrongSinIdentityMethodTrace = false := by
  decide +kernel

/-- Transparent replay proves the requested interval for the original
`sin (-x)` node in the checked extended expression program. -/
theorem extended_sin_neg_mem :
    semantics.Entails extendedProgram
      (initialContext checkerInput) checkerInput.target := by
  match result : checked? with
  | some evidence => exact evidence.proof
  | none =>
      have accepted := checked_isSome
      simp [result] at accepted

/-- Temporary vertical lift to the caller's original program.

The instance schema checks the same structural `sinNegExtends` theorem, but
the current generic replay API discards that evidence after validation and
has no cross-program stability law for `Semantics.holds`. This theorem is
therefore a canary to delete once replay returns a composed extension witness
and the fact semantics exposes that stability law. -/
theorem temporaryBaseSinNegMem :
    semantics.Entails baseProgram
      (initialContext checkerInput) checkerInput.target := by
  intro valuation model initial
  obtain ⟨extended, extendedModel, agreement⟩ :=
    sinNegExtends valuation model
  have extendedInitial :
      ∀ assumption, assumption ∈ initialContext checkerInput ->
        semantics.holds extendedProgram extended assumption := by
    intro assumption member
    have before : assumption.node.index < baseProgram.nodes.size := by
      have listed := member
      simp [initialContext, initialContextFrom, checkerInput] at listed
      rcases listed with equal | equal | equal
      all_goals subst assumption
      all_goals decide
    have holds := initial assumption member
    have equal := agreement assumption.node before
    change assumption.fact.Allows (valuation assumption.node) at holds
    change assumption.fact.Allows (extended assumption.node)
    rw [equal]
    exact holds
  have result :=
    extended_sin_neg_mem extended extendedModel extendedInitial
  have equal := agreement (node 2) (by decide)
  change Fact.negOneZero.Allows (extended (node 2)) at result
  change Fact.negOneZero.Allows (valuation (node 2))
  rw [equal] at result
  exact result

def concreteValuation (x : ℝ) : NodeId -> ℝ :=
    fun current =>
      if current = node 0 then x
      else if current = node 1 then -x
      else if current = node 2 then Real.sin (-x)
      else 0

theorem concreteModels (x : ℝ) : Models baseProgram (concreteValuation x) := by
  intro output current lookup
  rcases output with ⟨index⟩
  change baseProgram.nodes[index]? = some current at lookup
  obtain ⟨bound, currentEq⟩ := Array.getElem?_eq_some_iff.mp lookup
  change index < 3 at bound
  interval_cases index
  all_goals
    simp [baseProgram, instruction] at currentEq
    subst current
    simp [NodeMeaning, Program.operation?, baseProgram, operations,
      sourceOperation, negOperation, sinOperation, instruction,
      concreteValuation, node, sourceKey, negKey, sinKey]

/-- The structural program model is inhabited for every real source value;
the checked entailment is not vacuous. -/
theorem baseModelsNonempty (x : ℝ) :
    ∃ valuation, Models baseProgram valuation ∧ valuation (node 0) = x :=
  ⟨concreteValuation x, concreteModels x, by simp [concreteValuation, node]⟩

/-- The concrete Mathlib-facing theorem discharged by the arbitrary
propagator trace, modulo the explicitly temporary base-program lift above. -/
theorem realSinNegBounds :
    ∀ x : ℝ, 0 ≤ x -> x ≤ 2 ->
      -1 ≤ Real.sin (-x) ∧ Real.sin (-x) ≤ 0 := by
  intro x lower upper
  have initial :
      ∀ assumption, assumption ∈ initialContext checkerInput ->
        semantics.holds baseProgram (concreteValuation x) assumption := by
    intro assumption member
    simp [initialContext, initialContextFrom, checkerInput] at member
    rcases member with equal | equal | equal
    · subst assumption
      simpa [semantics, Fact.Allows, concreteValuation, node] using
        And.intro lower upper
    · subst assumption
      trivial
    · subst assumption
      trivial
  have result :=
    temporaryBaseSinNegMem (concreteValuation x) (concreteModels x) initial
  change Fact.negOneZero.Allows (concreteValuation x (node 2)) at result
  simpa [Fact.Allows, concreteValuation, node] using result

theorem realSinNegMemIcc (x : ℝ) (bounds : x ∈ Set.Icc (0 : ℝ) 2) :
    Real.sin (-x) ∈ Set.Icc (-1 : ℝ) 0 :=
  realSinNegBounds x bounds.1 bounds.2

end

end Hex.Interval.SinOddConformance
