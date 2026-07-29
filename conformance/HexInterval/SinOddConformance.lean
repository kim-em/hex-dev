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
import Mathlib.Tactic.Order

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
    match request.program.findOp? sinKey, request.program.findOp? negKey with
    | some (sinId, sinSignature), some (negId, negSignature) =>
      if sinSignature != sinOperation || negSignature != negOperation then
        { outcome := .inapplicable, drafts := [] }
      else
      { outcome :=
          .success []
            [.instantiate
              { key := 1
                nodes :=
                  [{ domain := real
                     op := sinId
                     args := [.existing binding.input] },
                   { domain := real
                     op := negId
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
    | _, _ => { outcome := .inapplicable, drafts := [] }

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
  { maxDecisions := 12
    maxTraversal := 512
    maxLiveOffers := 24 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 7
    maxBodyCells := 8
    maxDrafts := 7
    maxDraftCells := 8
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

noncomputable section

/-- Structural meaning of one node. The package interprets only its own
opaque operation keys; nodes owned by other packages remain unconstrained. -/
def NodeMeaning (program : Program) (valuation : NodeId -> ℝ)
    (output : NodeId) (instruction : Node) : Prop :=
  match program.operation? instruction.op with
  | none => False
  | some operation =>
      if operation.key = negKey then
        match instruction.args with
        | [input] =>
            if input.index < output.index then
              valuation output = -valuation input
            else
              True
        | _ => False
      else if operation.key = sinKey then
        match instruction.args with
        | [input] =>
            if input.index < output.index then
              valuation output = Real.sin (valuation input)
            else
              True
        | _ => False
      else
        True

/-- Whole-program structural semantics. This is not a lookup table for the
two programs used by the canary. -/
def Models (program : Program) (valuation : NodeId -> ℝ) : Prop :=
  ∀ output instruction, program.node? output = some instruction ->
    NodeMeaning program valuation output instruction

theorem nodeMeaning_congr (before after : Program)
    (valuation extended : NodeId -> ℝ) (output : NodeId) (current : Node)
    (operations : before.operations = after.operations)
    (outputValue : extended output = valuation output)
    (argumentValues : ∀ input, input.index < output.index ->
      extended input = valuation input) :
    NodeMeaning before valuation output current ↔
      NodeMeaning after extended output current := by
  have operationLookup :
      before.operation? current.op = after.operation? current.op := by
    simp [Program.operation?, operations]
  unfold NodeMeaning
  rw [← operationLookup]
  cases lookup : before.operation? current.op with
  | none => rfl
  | some operation =>
      by_cases negative : operation.key = negKey
      · cases current.args with
        | nil => simp [negative]
        | cons input rest =>
            cases rest with
            | nil =>
                by_cases inputBefore : input.index < output.index
                · have inputValue := argumentValues input inputBefore
                  simp [negative, inputBefore, outputValue, inputValue]
                · simp [negative, inputBefore]
            | cons next rest => simp [negative]
      · by_cases sine : operation.key = sinKey
        · cases current.args with
          | nil => simp [sine]
          | cons input rest =>
              cases rest with
              | nil =>
                  by_cases inputBefore : input.index < output.index
                  · have inputValue := argumentValues input inputBefore
                    simp [sine, inputBefore, outputValue, inputValue]
                  · simp [sine, inputBefore]
              | cons next rest => simp [sine]
        · simp [negative, sine]

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
  inputBefore : input.index < output.index

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
              if inputBefore : input.index < output.index then
                some
                  { instruction
                    operation
                    nodeProof
                    operationProof
                    keyProof
                    argsProof
                    inputBefore }
              else none
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
    shape.inputBefore, negKey] at meaning
  exact meaning

theorem UnaryShape.sinValue
    (shape : UnaryShape program sinKey output input)
    (model : Models program valuation) :
    valuation output = Real.sin (valuation input) := by
  have meaning := model output shape.instruction shape.nodeProof
  simp [NodeMeaning, shape.operationProof, shape.keyProof, shape.argsProof,
    shape.inputBefore, negKey, sinKey] at meaning
  exact meaning

theorem UnaryShape.outputBefore
    (shape : UnaryShape program key output input) :
    output.index < program.nodes.size := by
  have lookup := shape.nodeProof
  change program.nodes[output.index]? = some shape.instruction at lookup
  exact (Array.getElem?_eq_some_iff.mp lookup).1

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

/-- A checked, snapshot-local identifier for one unary real operation.  The
opaque key selects the package operation; its complete signature is checked
again before a certificate may use the compact identifier. -/
structure OperationShape (program : Program) (key : OpKey) where
  id : OpId
  operation : Operation
  lookup : program.operation? id = some operation
  keyProof : operation.key = key
  inputsProof : operation.inputs = [real]
  outputProof : operation.output = real

/-- Resolve an opaque operation key without assuming any global `OpId`
assignment or package-registration order. -/
def operationShape? (program : Program) (key : OpKey) :
    Option (OperationShape program key) := do
  let (id, operation) ← program.operationEntry? key
  if lookup : program.operation? id = some operation then
    if keyProof : operation.key = key then
      if inputsProof : operation.inputs = [real] then
        if outputProof : operation.output = real then
          some { id, operation, lookup, keyProof, inputsProof, outputProof }
        else none
      else none
    else none
  else none

def appendProgram (before : Program) (input : NodeId)
    (sinOperation negOperation : OpId) : Program :=
  { operations := before.operations
    nodes :=
      (before.nodes.push
        { domain := real, op := sinOperation, args := [input] }).push
        { domain := real
          op := negOperation
          args := [node before.nodes.size] } }

/-- The sine-oddness instantiator is conservative over every caller program,
not just over the small program used by the executable canary. -/
theorem appendExtends (before : Program) (input : NodeId)
    (sinOperation : OperationShape before sinKey)
    (negOperation : OperationShape before negKey)
    (inputOld : input.index < before.nodes.size) :
    semantics.Extends before
      (appendProgram before input sinOperation.id negOperation.id) := by
  intro valuation model
  let positive : NodeId := node before.nodes.size
  let negative : NodeId := node (before.nodes.size + 1)
  let extended : NodeId -> ℝ := fun current =>
    if current.index = positive.index then Real.sin (valuation input)
    else if current.index = negative.index then -Real.sin (valuation input)
    else valuation current
  refine ⟨extended, ?_, ?_⟩
  · intro output current lookup
    rcases output with ⟨index⟩
    change
      ((before.nodes.push
        { domain := real, op := sinOperation.id, args := [input] }).push
        { domain := real
          op := negOperation.id
          args := [node before.nodes.size] })[index]? = some current at lookup
    by_cases old : index < before.nodes.size
    · have oldLookup : before.node? { index } = some current := by
        change before.nodes[index]? = some current
        have notLast : index ≠ before.nodes.size + 1 := by omega
        simpa [Array.getElem?_push, Nat.ne_of_lt old, notLast] using lookup
      apply (nodeMeaning_congr before
        (appendProgram before input sinOperation.id negOperation.id)
        valuation extended { index } current rfl ?_ ?_).mp
        (model { index } current oldLookup)
      · have notPositive : index ≠ positive.index := by
          simp [positive, node]
          omega
        have notNegative : index ≠ negative.index := by
          simp [negative, node]
          omega
        simp [extended, notPositive, notNegative]
      · intro argument argumentBefore
        have argumentOld : argument.index < before.nodes.size :=
          Nat.lt_trans argumentBefore old
        have notPositive : argument.index ≠ positive.index := by
          simp [positive, node]
          omega
        have notNegative : argument.index ≠ negative.index := by
          simp [negative, node]
          omega
        simp [extended, notPositive, notNegative]
    · have bound : index < before.nodes.size + 2 := by
        obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp lookup
        simp only [Array.size_push] at bound
        omega
      have fresh : index = before.nodes.size ∨
          index = before.nodes.size + 1 := by omega
      rcases fresh with rfl | rfl
      · have expected :
            ((before.nodes.push
              { domain := real, op := sinOperation.id, args := [input] }).push
              { domain := real
                op := negOperation.id
                args := [node before.nodes.size] })[before.nodes.size]? =
              some { domain := real, op := sinOperation.id, args := [input] } := by
            rw [Array.getElem?_push]
            simp only [Array.size_push]
            have notLast : before.nodes.size ≠ before.nodes.size + 1 := by omega
            simp only [if_neg notLast]
            rw [Array.getElem?_push]
            simp
        rw [expected] at lookup
        injection lookup with currentEq
        symm at currentEq
        subst current
        have sinLookup :
            before.operations[sinOperation.id.index]? =
              some sinOperation.operation := by
          simpa [Program.operation?] using sinOperation.lookup
        have inputNotSize : input.index ≠ before.nodes.size := by omega
        have inputNotNext : input.index ≠ before.nodes.size + 1 := by omega
        simp [NodeMeaning, Program.operation?, appendProgram, sinLookup,
          sinOperation.keyProof, extended, positive, negative, node,
          inputNotSize, inputNotNext, negKey, sinKey]
      · have expected :
            ((before.nodes.push
              { domain := real, op := sinOperation.id, args := [input] }).push
              { domain := real
                op := negOperation.id
                args := [node before.nodes.size] })[before.nodes.size + 1]? =
              some
                { domain := real
                  op := negOperation.id
                  args := [node before.nodes.size] } := by
            rw [Array.getElem?_push]
            simp
        rw [expected] at lookup
        injection lookup with currentEq
        symm at currentEq
        subst current
        have negLookup :
            before.operations[negOperation.id.index]? =
              some negOperation.operation := by
          simpa [Program.operation?] using negOperation.lookup
        simp [NodeMeaning, Program.operation?, appendProgram, negLookup,
          negOperation.keyProof, extended, positive, negative, node,
          negKey, sinKey]
  · intro current old
    have notPositive : current.index ≠ positive.index := by
      simp [positive, node]
      omega
    have notNegative : current.index ≠ negative.index := by
      simp [negative, node]
      omega
    simp [extended, notPositive, notNegative]

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
    replay := fun _ action context _ => do
      if action.key != sinNegInstantiateKey ||
          action.kind != .instantiate then none
      else pure ()
      let outer ← unaryWitness? context.before sinKey action.node
      let inner ← unaryWitness? context.before negKey outer.input
      let sinOperation ← operationShape? context.before sinKey
      let negOperation ← operationShape? context.before negKey
      let positive := node context.before.nodes.size
      let negative := node (context.before.nodes.size + 1)
      let expected := appendProgram context.before inner.input
        sinOperation.id negOperation.id
      if context.event.substitution != [action.node] ||
          context.event.products != [positive, negative] ||
          context.event.newNodes != [positive, negative] then none
      else pure ()
      if afterProof : context.after = expected then
        some
          { proof := by
              rw [afterProof]
              exact appendExtends context.before inner.input
                sinOperation negOperation
                (Nat.lt_trans inner.shape.inputBefore
                  inner.shape.outputBefore) }
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

/-! ## Arbitrary-caller structural canaries -/

def foreignKey : OpKey := { name := "sin-odd.foreign" }

def foreignOperation : Operation :=
  { key := foreignKey, inputs := [], output := real }

/-- The same `sin (-x)` shape in a caller program with an unrelated old node
and a completely different compact operation ordering. -/
def reorderedProgram : Program :=
  { operations := #[foreignOperation, sinOperation, sourceOperation, negOperation]
    nodes :=
      #[instruction 2,
        instruction 0,
        instruction 3 [node 0],
        instruction 1 [node 2]] }

def reorderedAfter : Program :=
  appendProgram reorderedProgram (node 0) { index := 1 } { index := 3 }

def reorderedAction : Action :=
  { instantiateAction with node := node 3 }

def reorderedEvent : InstanceEvent :=
  { instanceEvent with
    origin := reorderedAction
    substitution := [node 3]
    products := [node 4, node 5]
    newNodes := [node 4, node 5]
    equalities := [] }

def reorderedInput : CheckerInput Fact :=
  { baseProgram := reorderedProgram
    initialFacts := #[]
    target := { node := node 3, fact := .top } }

def instanceAcceptedWith (event : InstanceEvent) (after : Program) : Bool :=
  let context : InstanceContext reorderedInput reorderedAction :=
    { before := reorderedProgram
      after
      basePrefix := ProgramPrefix.refl reorderedProgram
      event }
  match instanceSchema.decode [0] with
  | none => false
  | some certificate =>
      (instanceSchema.replay reorderedInput reorderedAction context
        certificate).isSome

def instanceAccepted (after : Program) : Bool :=
  instanceAcceptedWith reorderedEvent after

/-- Stable-key resolution and structural replay work independently of both
operation order and unrelated nodes already present in the caller graph. -/
theorem accepts_reordered_instance :
    instanceAccepted reorderedAfter = true := by
  decide +kernel

def wrongReorderedAfter : Program :=
  appendProgram reorderedProgram (node 0) { index := 3 } { index := 1 }

/-- The same event metadata cannot certify a different appended expression
recipe. -/
theorem rejects_wrong_append :
    instanceAccepted wrongReorderedAfter = false := by
  decide +kernel

def wrongProductsEvent : InstanceEvent :=
  { reorderedEvent with products := [node 5, node 4] }

/-- The extension theorem is tied to the exact fresh-node products recorded by
the instance event, not merely to an equal-sized program suffix. -/
theorem rejects_wrong_products :
    instanceAcceptedWith wrongProductsEvent reorderedAfter = false := by
  decide +kernel

def wrongSinSignature : Program :=
  { operations := #[{ key := sinKey, inputs := [], output := real }]
    nodes := #[] }

/-- An opaque key match does not excuse a mismatched operation signature. -/
theorem rejects_wrong_signature :
    (operationShape? wrongSinSignature sinKey).isNone = true := by
  decide +kernel

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
      (semantics.Entails baseProgram
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

/-- The generic checker composes the package-owned extension proof and returns
the requested interval directly over the caller's original program. -/
theorem checkedSinNegMem :
    semantics.Entails baseProgram
      (initialContext checkerInput) checkerInput.target := by
  match result : checked? with
  | some evidence => exact evidence.proof
  | none =>
      have accepted := checked_isSome
      simp [result] at accepted

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
propagator trace and the generic base-program lift. -/
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
    checkedSinNegMem (concreteValuation x) (concreteModels x) initial
  change Fact.negOneZero.Allows (concreteValuation x (node 2)) at result
  simpa [Fact.Allows, concreteValuation, node] using result

theorem realSinNegMemIcc (x : ℝ) (bounds : x ∈ Set.Icc (0 : ℝ) 2) :
    Real.sin (-x) ∈ Set.Icc (-1 : ℝ) 0 :=
  realSinNegBounds x bounds.1 bounds.2

end

end Hex.Interval.SinOddConformance
