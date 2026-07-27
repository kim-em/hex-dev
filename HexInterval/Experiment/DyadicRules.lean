/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.DyadicInterval

@[expose] public section

/-!
# Concrete dyadic propagators

This module is the first registry whose rules assign real function semantics to
the otherwise opaque interval engine.  The engine still interprets none of the
operation or rule keys below.  Each callback sees only its declared facts plus
the immutable structural program view, and every proposed fact crosses the
engine-owned intersection boundary.

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
def centeredOp : OpKey := { name := "real.centered-product" }

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
def centeredInstantiateKey : RuleKey := { name := "real.centered-product.instantiate" }

/-- Operation signatures which a real-valued frontend may splice into its own
operation table.  The registry dispatches by key, never by these positions. -/
def operations (real : DomainId) : Array Operation :=
  #[{ key := oneOp, inputs := [], output := real },
    { key := negOp, inputs := [real], output := real },
    { key := subOp, inputs := [real, real], output := real },
    { key := mulOp, inputs := [real, real], output := real },
    { key := squareOp, inputs := [real], output := real },
    { key := reciprocalOp, inputs := [real], output := real },
    { key := centeredOp, inputs := [real], output := real }]

/-! ## Registrations -/

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

/-- A discovery rule for products.  It reads no interval facts: its semantic
dependency is the immutable nested expression shape. -/
def centeredInstantiate : Registration :=
  { key := centeredInstantiateKey
    head := mulOp
    kind := .instantiate
    watches := []
    writes := [] }

def registrations : Array Registration :=
  #[negForward, negBackward, subForward, subLeft, subRight,
    mulForward, mulLeft, mulRight, squareForward,
    reciprocalForward, reciprocalBackward, centeredForward,
    centeredInstantiate]

/-! ## Registry configuration and result conversion -/

structure Config where
  endpointLimit : EndpointLimit
  reciprocalBasePrecision : Precision
  maxReciprocalEffort : Nat

structure Registry where
  config : Config

def Config.precisionAt (config : Config) (effort : Nat) : Precision :=
  config.reciprocalBasePrecision + Int.ofNat effort

def successCost (arithmeticWork proofNodes : Nat) : CostObservation :=
  { arithmeticWork, estimatedProofNodes := proofNodes }

def outcomeOfResult (target : NodeId) (payload work proofNodes : Nat)
    (suggestions : List Suggestion) : DyadicInterval.Result -> Outcome Fact
  | .ready fact =>
      .success [{ node := target, fact, payload := { index := payload } }]
        suggestions (successCost work proofNodes)
  | .inapplicable => .inapplicable
  | .resourceLimit cost => .resourceLimit (DyadicInterval.workMagnitude cost)

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

def invokeNegForward (config : Config) (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [input], [target] =>
      outcomeOfResult target 10 1 1 [] (DyadicInterval.neg config.endpointLimit input.fact)
  | _, _ => .failed 10

def invokeNegBackward (config : Config) (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [output], [target] =>
      outcomeOfResult target 11 1 1 [] (DyadicInterval.neg config.endpointLimit output.fact)
  | _, _ => .failed 11

def invokeSubForward (config : Config) (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [left, right], [target] =>
      outcomeOfResult target 20 1 1 []
        (DyadicInterval.sub config.endpointLimit left.fact right.fact)
  | _, _ => .failed 20

def invokeSubLeft (config : Config) (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [output, right], [target] =>
      outcomeOfResult target 21 2 2 []
        (addViaSub config.endpointLimit output.fact right.fact)
  | _, _ => .failed 21

def invokeSubRight (config : Config) (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [left, output], [target] =>
      outcomeOfResult target 22 1 1 []
        (DyadicInterval.sub config.endpointLimit left.fact output.fact)
  | _, _ => .failed 22

def invokeMulForward (config : Config) (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [left, right], [target] =>
      outcomeOfResult target 30 1 1 []
        (DyadicInterval.mul config.endpointLimit left.fact right.fact)
  | _, _ => .failed 30

def invokeMulLeft (config : Config) (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [output, right], [target] =>
      match singleton? right.fact with
      | none => .inapplicable
      | some scalar =>
          outcomeOfResult target 31 1 1 []
            (DyadicInterval.unscaleExact config.endpointLimit scalar output.fact)
  | _, _ => .failed 31

def invokeMulRight (config : Config) (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [output, left], [target] =>
      match singleton? left.fact with
      | none => .inapplicable
      | some scalar =>
          outcomeOfResult target 32 1 1 []
            (DyadicInterval.unscaleExact config.endpointLimit scalar output.fact)
  | _, _ => .failed 32

def invokeSquareForward (config : Config) (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [input], [target] =>
      outcomeOfResult target 40 1 1 []
        (DyadicInterval.square config.endpointLimit input.fact)
  | _, _ => .failed 40

def invokeReciprocalForward (config : Config)
    (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [input], [target] =>
      outcomeOfResult target (50 + request.action.effort) 1 1
        (retrySuggestion config request.action)
        (DyadicInterval.reciprocal config.endpointLimit
          (config.precisionAt request.action.effort) input.fact)
  | _, _ => .failed 50

def invokeReciprocalBackward (config : Config)
    (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [output], [target] =>
      outcomeOfResult target (60 + request.action.effort) 1 1
        (retrySuggestion config request.action)
        (DyadicInterval.reciprocal config.endpointLimit
          (config.precisionAt request.action.effort) output.fact)
  | _, _ => .failed 60

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
    (request : RuleRequest Fact) : Outcome Fact :=
  match request.inputs, request.writes with
  | [input], [target] =>
      outcomeOfResult target 70 4 4 []
        (centeredImage config.endpointLimit input.fact)
  | _, _ => .failed 70

structure CenteredBinding where
  anchor : NodeId
  input : NodeId
  complement : NodeId
  one : NodeId

def operationWithKey? (view : ProgramView) (key : OpKey) : Option OpId := do
  for index in [0:view.operations.size] do
    let operation <- view.operations[index]?
    if operation.key == key then return { index }
  none

def findProgramNode? (view : ProgramView) (target : Node) : Option NodeId :=
  Propagator.findNodeFrom 0 view.nodes.toList target

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
  pure { anchor := request.action.node, input, complement, one }

/-- Match the engine's authoritative generation calculation for this concrete
proposal: invocation substitution, existing proposal references, and a CSE hit
if the centered node already exists. -/
def centeredGeneration? (request : RuleRequest Fact) (binding : CenteredBinding)
    (centered : Node) : Option Nat := do
  let cse := findProgramNode? request.program centered
  let references := dedupList
    (request.action.node :: request.action.inputs.map (fun input => input.node) ++
      [binding.input] ++ cse.toList)
  let generations <- references.mapM request.program.generation?
  pure (generations.foldl Nat.max 0 + 1)

def centeredProposal? (request : RuleRequest Fact)
    (binding : CenteredBinding) : Option InstantiationRequest := do
  let input <- request.program.node? binding.input
  let operation <- operationWithKey? request.program centeredOp
  let centered : Node := { domain := input.domain, op := operation, args := [binding.input] }
  let generation <- centeredGeneration? request binding centered
  pure
    { key := 1
      triggers := [binding.anchor, binding.input, binding.complement, binding.one]
      claimedGeneration := generation
      nodes :=
        [{ domain := input.domain
           op := operation
           args := [.existing binding.input] }]
      equalities :=
        [{ left := .existing binding.anchor
           right := .proposed 0
           payload := { index := 81 } }]
      payload := { index := 80 } }

def invokeCenteredInstantiate (request : RuleRequest Fact) : Outcome Fact :=
  match centeredBinding? request >>= centeredProposal? request with
  | none => .inapplicable
  | some proposal =>
      .success [] [.instantiate proposal]
        { visitedEntries := request.program.operations.size + request.program.nodes.size
          estimatedProofNodes := 1 }

/-! ## Versioned dispatch -/

def Registry.invoke (registry : Registry) (request : RuleRequest Fact) : Outcome Fact :=
  let key := request.action.key
  if key == negForwardKey then invokeNegForward registry.config request
  else if key == negBackwardKey then invokeNegBackward registry.config request
  else if key == subForwardKey then invokeSubForward registry.config request
  else if key == subLeftKey then invokeSubLeft registry.config request
  else if key == subRightKey then invokeSubRight registry.config request
  else if key == mulForwardKey then invokeMulForward registry.config request
  else if key == mulLeftKey then invokeMulLeft registry.config request
  else if key == mulRightKey then invokeMulRight registry.config request
  else if key == squareForwardKey then invokeSquareForward registry.config request
  else if key == reciprocalForwardKey then invokeReciprocalForward registry.config request
  else if key == reciprocalBackwardKey then invokeReciprocalBackward registry.config request
  else if key == centeredForwardKey then invokeCenteredForward registry.config request
  else if key == centeredInstantiateKey then invokeCenteredInstantiate request
  else .failed 255

def Registry.invokeWithCache (registry : Registry) (cache : Cache)
    (request : RuleRequest Fact) : Outcome Fact × Cache :=
  (registry.invoke request, cache)

end Hex.Interval.Experiment.DyadicRules
