/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.DyadicInterval
public import HexInterval.Experiment.PackageRegistry

@[expose] public section

/-!
# Concrete dyadic propagators

This module is the first composed registry whose rules assign real function
semantics to the otherwise opaque interval engine.  Arithmetic and the
centered function are independent packages with callback routes assembled from
the same registrations given to the engine.  The engine still interprets none
of the operation or rule keys below.  Each callback sees only its declared
facts plus the immutable structural program view, and every proposed fact
crosses the engine-owned intersection boundary.

The arithmetic surface is intentionally smaller than the eventual registry.
Multiplication contracts backwards only when the other factor is a singleton
with an exact dyadic reciprocal.  Reciprocal uses the sign-separated component
operation from `DyadicInterval`; a fact containing zero remains explicitly
inapplicable until the total-inverse hull and interval-set experiments land.
-/

namespace Hex.Interval.Experiment.DyadicRules

open Propagator

abbrev Fact := DyadicInterval.Fact

/-! ## Stable semantic keys -/

def oneOp : OpKey := { name := "real.one" }
def negOp : OpKey := { name := "real.neg" }
def subOp : OpKey := { name := "real.sub" }
def mulOp : OpKey := { name := "real.mul" }
def squareOp : OpKey := { name := "real.square" }
def reciprocalOp : OpKey := { name := "real.reciprocal" }
/-- Version 1 denotes exactly the function `x ↦ 1/4 - (x - 1/2)^2`. -/
def centeredOp : OpKey := { name := "real.centered-product" }

def oneForwardKey : RuleKey := { name := "real.one.forward" }
def negForwardKey : RuleKey := { name := "real.neg.forward" }
def negBackwardKey : RuleKey := { name := "real.neg.backward" }
def subForwardKey : RuleKey := { name := "real.sub.forward" }
def subLeftKey : RuleKey := { name := "real.sub.backward-left" }
def subRightKey : RuleKey := { name := "real.sub.backward-right" }
def mulForwardKey : RuleKey := { name := "real.mul.forward" }
def mulLeftKey : RuleKey := { name := "real.mul.backward-left-singleton" }
def mulRightKey : RuleKey := { name := "real.mul.backward-right-singleton" }
def squareForwardKey : RuleKey := { name := "real.square.forward" }
def reciprocalForwardKey : RuleKey := { name := "real.reciprocal.forward" }
def reciprocalBackwardKey : RuleKey := { name := "real.reciprocal.backward" }
def centeredForwardKey : RuleKey := { name := "real.centered-product.forward" }
def centeredSplitKey : RuleKey := { name := "real.centered-product.split-critical" }
def centeredInstantiateKey : RuleKey := { name := "real.centered-product.instantiate" }

/-- Operation signatures for the elementary arithmetic package. -/
def arithmeticOperations (real : DomainId) : Array Operation :=
  #[{ key := oneOp, inputs := [], output := real },
    { key := negOp, inputs := [real], output := real },
    { key := subOp, inputs := [real, real], output := real },
    { key := mulOp, inputs := [real, real], output := real },
    { key := squareOp, inputs := [real], output := real },
    { key := reciprocalOp, inputs := [real], output := real }]

/-- Operation signatures for the independent centered-product package. -/
def centeredOperations (real : DomainId) : Array Operation :=
  #[{ key := centeredOp, inputs := [real], output := real }]

/-- Arithmetic signatures whose shape and meaning the centered matcher uses
without owning their implementations. -/
def centeredRequirements (real : DomainId) : Array Operation :=
  #[{ key := oneOp, inputs := [], output := real },
    { key := subOp, inputs := [real, real], output := real },
    { key := mulOp, inputs := [real, real], output := real }]

/-! ## Registrations -/

def oneForward : Registration :=
  { key := oneForwardKey
    head := oneOp
    kind := .forward
    watches := []
    writes := [.result] }

def negForward : Registration :=
  { key := negForwardKey
    head := negOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def negBackward : Registration :=
  { key := negBackwardKey
    head := negOp
    kind := .backward
    watches := [.result]
    writes := [.argument 0] }

def subForward : Registration :=
  { key := subForwardKey
    head := subOp
    kind := .forward
    watches := [.argument 0, .argument 1]
    writes := [.result] }

def subLeft : Registration :=
  { key := subLeftKey
    head := subOp
    kind := .backward
    watches := [.result, .argument 1]
    writes := [.argument 0] }

def subRight : Registration :=
  { key := subRightKey
    head := subOp
    kind := .backward
    watches := [.argument 0, .result]
    writes := [.argument 1] }

def mulForward : Registration :=
  { key := mulForwardKey
    head := mulOp
    kind := .forward
    watches := [.argument 0, .argument 1]
    writes := [.result] }

def mulLeft : Registration :=
  { key := mulLeftKey
    head := mulOp
    kind := .backward
    watches := [.result, .argument 1]
    writes := [.argument 0] }

def mulRight : Registration :=
  { key := mulRightKey
    head := mulOp
    kind := .backward
    watches := [.result, .argument 0]
    writes := [.argument 1] }

def squareForward : Registration :=
  { key := squareForwardKey
    head := squareOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def reciprocalForward : Registration :=
  { key := reciprocalForwardKey
    head := reciprocalOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def reciprocalBackward : Registration :=
  { key := reciprocalBackwardKey
    head := reciprocalOp
    kind := .backward
    watches := [.result]
    writes := [.argument 0] }

def centeredForward : Registration :=
  { key := centeredForwardKey
    head := centeredOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

/-- A function-owned semantic landmark.  Selecting it creates solver branches;
the rule itself has no branch-construction authority. -/
def centeredSplit : Registration :=
  { key := centeredSplitKey
    head := centeredOp
    kind := .split
    watches := [.argument 0]
    writes := [] }

/-- A discovery rule for products. It reads no interval facts and inspects
only its anchor's immutable argument sub-DAG plus the operation table, so an
unrelated program extension is not a dependency. -/
def centeredInstantiate : Registration :=
  { key := centeredInstantiateKey
    head := mulOp
    kind := .instantiate
    watches := []
    writes := [] }

/-! ## Registry configuration and result conversion -/

structure Config where
  endpointLimit : EndpointLimit
  reciprocalBasePrecision : Precision
  maxReciprocalEffort : Nat

/-! ## Reply-local proof payloads

Labels distinguish uses only within one callback reply. Payload-schema-zero
recipes have empty bodies: after freezing, replay dispatch is determined by
the engine-owned origin rule compatibility epoch, semantic role, and payload
schema. This deliberately avoids a second central recipe tag alongside
`PayloadArena.Entry.origin`.
-/

def factLabel : PayloadId := { index := 0 }
def instanceLabel : PayloadId := { index := 1 }
def equalityLabel : PayloadId := { index := 2 }

def emptyDraft (label : PayloadId) (role : PayloadArena.Role) :
    PayloadArena.Draft :=
  { label, role, schema := 0, body := [] }

/-- Payload-schema-zero dyadic recipes have no body cells. Exact empty-list
matching rejects trailing data instead of silently accepting a future recipe
variant. -/
def emptyFormat (role : PayloadArena.Role) : ReplayFormat :=
  { role
    schema := 0
    validateBody := fun body =>
      match body with
      | [] => true
      | _ :: _ => false }

def factHandler (registration : Registration)
    (invoke : RuleRequest Fact -> Plan Fact) : Handler Fact Unit :=
  Handler.statelessPlanned registration invoke #[emptyFormat .fact]

def withoutPayloads (outcome : Outcome Fact) : Plan Fact :=
  { outcome, drafts := [] }

def centeredFamilyKey : Nat := 1

def Config.precisionAt (config : Config) (effort : Nat) : Precision :=
  config.reciprocalBasePrecision + Int.ofNat effort

def precisionAllowed (limit : EndpointLimit) (precision : Precision) : Bool :=
  let magnitude := precision.natAbs
  magnitude ≤ limit.maxEndpointHeight &&
    EndpointCost.natBits magnitude ≤ limit.maxEndpointHeight

/-- Effort raises precision monotonically, so the greatest absolute precision
over the configured effort interval occurs at one of its endpoints. -/
def Config.reciprocalPrecisionsAllowed (config : Config) : Bool :=
  precisionAllowed config.endpointLimit config.reciprocalBasePrecision &&
    precisionAllowed config.endpointLimit
      (config.precisionAt config.maxReciprocalEffort)

def successCost (arithmeticWork proofNodes : Nat) : CostObservation :=
  { arithmeticWork, estimatedProofNodes := proofNodes }

def planOfResult (target : NodeId) (work proofNodes : Nat)
    (suggestions : List Suggestion) : DyadicInterval.Result -> Plan Fact
  | .ready fact =>
      { outcome :=
          .success [{ node := target, fact, payload := factLabel }]
            suggestions (successCost work proofNodes)
        drafts := [emptyDraft factLabel .fact] }
  | .inapplicable => withoutPayloads .inapplicable
  | .resourceLimit cost =>
      withoutPayloads (.resourceLimit (DyadicInterval.workCode cost))

def bindResult (result : DyadicInterval.Result)
    (next : Fact -> DyadicInterval.Result) : DyadicInterval.Result :=
  match result with
  | .ready fact => next fact
  | .inapplicable => .inapplicable
  | .resourceLimit cost => .resourceLimit cost

/-- Addition expressed through the already checked primitives.  This is used
only by the backward contractor for `z = x - y`. -/
def addViaSub (limit : EndpointLimit) (left right : Fact) : DyadicInterval.Result :=
  bindResult (DyadicInterval.neg limit right) fun negative =>
    DyadicInterval.sub limit left negative

/-- Recognize an attained singleton.  Canonical `Dyadic` equality is structural
and does not align exponents or allocate shifted integers. -/
def singleton? (fact : Fact) : Option Dyadic :=
  match fact.view with
  | .bounds (.finite lower false) (.finite upper false) =>
      if lower = upper then some lower else none
  | .empty | .bounds _ _ => none

def retrySuggestion (config : Config) (action : Action) : List Suggestion :=
  if action.effort < config.maxReciprocalEffort then
    [.retry (action.effort + 1)]
  else
    []

/-! ## Arithmetic callbacks -/

def invokeOneForward (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [], [target] =>
      planOfResult target 1 1 []
        (DyadicInterval.closed config.endpointLimit 1 1)
  | _, _ => withoutPayloads (.failed 1)

def invokeNegForward (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [input], [target] =>
      planOfResult target 1 1 []
        (DyadicInterval.neg config.endpointLimit input.fact)
  | _, _ => withoutPayloads (.failed 10)

def invokeNegBackward (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [output], [target] =>
      planOfResult target 1 1 []
        (DyadicInterval.neg config.endpointLimit output.fact)
  | _, _ => withoutPayloads (.failed 11)

def invokeSubForward (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [left, right], [target] =>
      planOfResult target 1 1 []
        (DyadicInterval.sub config.endpointLimit left.fact right.fact)
  | _, _ => withoutPayloads (.failed 20)

def invokeSubLeft (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [output, right], [target] =>
      planOfResult target 2 2 []
        (addViaSub config.endpointLimit output.fact right.fact)
  | _, _ => withoutPayloads (.failed 21)

def invokeSubRight (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [left, output], [target] =>
      planOfResult target 1 1 []
        (DyadicInterval.sub config.endpointLimit left.fact output.fact)
  | _, _ => withoutPayloads (.failed 22)

def invokeMulForward (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [left, right], [target] =>
      planOfResult target 1 1 []
        (DyadicInterval.mul config.endpointLimit left.fact right.fact)
  | _, _ => withoutPayloads (.failed 30)

def invokeMulLeft (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [output, right], [target] =>
      match singleton? right.fact with
      | none => withoutPayloads .inapplicable
      | some scalar =>
          planOfResult target 1 1 []
            (DyadicInterval.unscaleExact config.endpointLimit scalar output.fact)
  | _, _ => withoutPayloads (.failed 31)

def invokeMulRight (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [output, left], [target] =>
      match singleton? left.fact with
      | none => withoutPayloads .inapplicable
      | some scalar =>
          planOfResult target 1 1 []
            (DyadicInterval.unscaleExact config.endpointLimit scalar output.fact)
  | _, _ => withoutPayloads (.failed 32)

def invokeSquareForward (config : Config) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [input], [target] =>
      planOfResult target 1 1 []
        (DyadicInterval.square config.endpointLimit input.fact)
  | _, _ => withoutPayloads (.failed 40)

def invokeReciprocalForward (config : Config)
    (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [input], [target] =>
      planOfResult target 1 1
        (retrySuggestion config request.action)
        (DyadicInterval.reciprocal config.endpointLimit
          (config.precisionAt request.action.effort) input.fact)
  | _, _ => withoutPayloads (.failed 50)

def invokeReciprocalBackward (config : Config)
    (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [output], [target] =>
      planOfResult target 1 1
        (retrySuggestion config request.action)
        (DyadicInterval.reciprocal config.endpointLimit
          (config.precisionAt request.action.effort) output.fact)
  | _, _ => withoutPayloads (.failed 60)

/-! ## Centered arbitrary function and shape-triggered instantiation -/

def half : Dyadic := Dyadic.ofIntWithPrec 1 1
def quarter : Dyadic := Dyadic.ofIntWithPrec 1 2

/-- Enclose `1/4 - (x - 1/2)^2`.  This is a function-specific propagator, not
an identity known by the engine. -/
def centeredImage (limit : EndpointLimit) (input : Fact) : DyadicInterval.Result :=
  bindResult (DyadicInterval.closed limit half half) fun halfFact =>
    bindResult (DyadicInterval.sub limit input halfFact) fun shifted =>
      bindResult (DyadicInterval.square limit shifted) fun squared =>
        bindResult (DyadicInterval.closed limit quarter quarter) fun quarterFact =>
          DyadicInterval.sub limit quarterFact squared

def invokeCenteredForward (config : Config)
    (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [input], [target] =>
      planOfResult target 4 4 []
        (centeredImage config.endpointLimit input.fact)
  | _, _ => withoutPayloads (.failed 70)

def invokeCenteredSplit (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [input], [] =>
      .success []
        [.split { node := input.node, point := half, reason := .criticalPoint }]
        { visitedEntries := 1, estimatedProofNodes := 1 }
  | _, _ => .failed 71

structure CenteredBinding where
  anchor : NodeId
  input : NodeId

def centeredBinding? (request : RuleRequest Fact) : Option CenteredBinding := do
  if request.program.programVersion != request.action.programVersion then none else pure ()
  let product <- request.program.node? request.action.node
  if request.program.operationKey? request.action.node != some mulOp then none else pure ()
  let [input, complement] := product.args | none
  let difference <- request.program.node? complement
  if request.program.operationKey? complement != some subOp then none else pure ()
  let [one, repeated] := difference.args | none
  if repeated != input then none else pure ()
  if request.program.operationKey? one != some oneOp then none else pure ()
  pure { anchor := request.action.node, input }

def centeredProposal? (request : RuleRequest Fact)
    (binding : CenteredBinding) : Option InstantiationRequest := do
  let input <- request.program.node? binding.input
  let (operation, signature) <- request.program.findOp? centeredOp
  if input.domain != signature.output then none else pure ()
  pure
    { key := centeredFamilyKey
      nodes :=
        [{ domain := signature.output
           op := operation
           args := [.existing binding.input] }]
      equalities :=
        [{ left := .existing binding.anchor
           right := .proposed 0
           payload := equalityLabel }]
      payload := instanceLabel }

/-- Propose the package-owned identity
`x * (1 - x) = 1/4 - (x - 1/2)^2`. Its instantiation and equality evidence
use distinct reply-local labels and schema-zero replay formats. -/
def invokeCenteredInstantiate (request : RuleRequest Fact) : Plan Fact :=
  match centeredBinding? request >>= centeredProposal? request with
  | none => withoutPayloads .inapplicable
  | some proposal =>
      { outcome :=
          .success [] [.instantiate proposal]
            { visitedEntries := request.program.operations.size + request.program.nodes.size
              estimatedProofNodes := 1 }
        drafts :=
          [emptyDraft instanceLabel .instance,
            emptyDraft equalityLabel .equality] }

/-! ## Independently composable function packages -/

def arithmeticPackage (config : Config) (real : DomainId) : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := arithmeticOperations real
    handlers :=
      #[factHandler oneForward (invokeOneForward config),
        factHandler negForward (invokeNegForward config),
        factHandler negBackward (invokeNegBackward config),
        factHandler subForward (invokeSubForward config),
        factHandler subLeft (invokeSubLeft config),
        factHandler subRight (invokeSubRight config),
        factHandler mulForward (invokeMulForward config),
        factHandler mulLeft (invokeMulLeft config),
        factHandler mulRight (invokeMulRight config),
        factHandler squareForward (invokeSquareForward config),
        factHandler reciprocalForward (invokeReciprocalForward config),
        factHandler reciprocalBackward (invokeReciprocalBackward config)]
    acceptsLimits := fun _ limits _ =>
      config.maxReciprocalEffort ≤ limits.maxEffort &&
        config.reciprocalPrecisionsAllowed &&
        2 ≤ limits.maxObservationValue && 60 ≤ limits.maxDiagnosticValue &&
        1 ≤ limits.maxOutcomeCandidates &&
        (config.maxReciprocalEffort == 0 || 1 ≤ limits.maxOutcomeSuggestions) }

/-- This package contributes one operation but also attaches its structural
matcher to multiplication from the arithmetic package. -/
def centeredPackage (config : Config) (real : DomainId) : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    requiredOperations := centeredRequirements real
    handlers :=
      #[factHandler centeredForward (invokeCenteredForward config),
        Handler.statelessDroppingDrafts centeredSplit invokeCenteredSplit,
        Handler.statelessPlanned centeredInstantiate invokeCenteredInstantiate
          #[emptyFormat .instance, emptyFormat .equality]]
    acceptsLimits := fun _ limits _ =>
      4 ≤ limits.maxObservationValue &&
        71 ≤ limits.maxDiagnosticValue &&
        1 ≤ limits.maxOutcomeCandidates && 1 ≤ limits.maxOutcomeSuggestions &&
        4 ≤ limits.maxProposalItems &&
        (EndpointCost.ofDyadic half).allowed limits.splitEndpointLimit &&
        limits.maxOperations ≤ limits.maxObservationValue &&
        limits.maxNodes ≤ limits.maxObservationValue - limits.maxOperations }

def buildRegistry (config : Config) (real : DomainId) (limits : Hex.Interval.State.Limits) :
    Except RegistryError (Propagator.Registry Fact) :=
  Propagator.Registry.buildWithin limits
    #[arithmeticPackage config real, centeredPackage config real]

/-- The legacy search-only driver allocates no proof payloads. Packages used
through it must therefore accept the empty arena envelope as well as the
engine limits. Proof-producing execution supplies its real envelope through
`PayloadSession`. -/
def searchArenaLimits : PayloadArena.Limits :=
  { maxEntries := 0
    maxBodyCells := 0
    maxDrafts := 0
    maxDraftCells := 0
    maxAtom := 0
    maxSchema := 0
    maxUses := 0 }

inductive StartError where
  | incompatibleLimits
  | registry (error : RegistryError)
  | operationMismatch
  | engine (error : DyadicInterval.StartError)
  deriving DecidableEq, Repr

/-- The checked entry point binds the exact flattened registrations to their
callbacks and retains the existential registry as the driver's cache. -/
def start (config : Config) (real : DomainId) (program : Program)
    (rawFacts : Array Raw) (limits : Hex.Interval.State.Limits) :
    Except StartError (Engine Fact × Propagator.Registry Fact) :=
  match buildRegistry config real limits with
  | .error error => .error (.registry error)
  | .ok registry =>
      match preflightStart program registry.registrations rawFacts.size limits with
      | .error error => .error (.engine (.engine error))
      | .ok () =>
          if !registry.acceptsProgram program then .error .operationMismatch
          else if !registry.acceptsLimits program limits searchArenaLimits then
            .error .incompatibleLimits
          else
            match DyadicInterval.start config.endpointLimit program registry.registrations
                rawFacts limits with
            | .error error => .error (.engine error)
            | .ok engine => .ok (engine, registry)

end Hex.Interval.Experiment.DyadicRules
