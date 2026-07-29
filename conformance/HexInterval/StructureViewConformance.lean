/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Propagator

/-!
Conformance canaries for shape-triggered arbitrary propagators.

All operation names below are opaque to the engine.  The external registry
recognizes a product whose right child has the repeated-variable shape
`one - x`, then proposes another opaque node and an equality.  Its rules watch
no facts, so the test also checks that structural matching does not grant
undeclared fact access.
-/

namespace Hex.Interval.StructureViewConformance

open Experiment.Propagator

abbrev Fact := Nat

def domain : DomainId := { index := 0 }

def xOp : OpKey := { name := "shape.x" }
def yOp : OpKey := { name := "shape.y" }
def oneOp : OpKey := { name := "shape.one" }
def seedOp : OpKey := { name := "shape.seed" }
def subOp : OpKey := { name := "shape.sub" }
def mulOp : OpKey := { name := "shape.mul" }
def centeredOp : OpKey := { name := "shape.centered" }

def appendKey : RuleKey := { name := "shape.append-product" }
def centeredKey : RuleKey := { name := "shape.center-product" }

def node (index : Nat) : NodeId := { index }
def suggestion (index : Nat) : SuggestionId := { index }

def operations : Array Operation :=
  #[{ key := xOp, inputs := [], output := domain },
    { key := yOp, inputs := [], output := domain },
    { key := oneOp, inputs := [], output := domain },
    { key := seedOp, inputs := [domain], output := domain },
    { key := subOp, inputs := [domain, domain], output := domain },
    { key := mulOp, inputs := [domain, domain], output := domain },
    { key := centeredOp, inputs := [domain], output := domain }]

def instruction (op : Nat) (args : List NodeId := []) : Node :=
  { domain, op := { index := op }, args }

/-- Nodes 5, 7, and 8 share the same product head.  Only node 5 is the
repeated-variable shape `x * (one - x)`. -/
def program : Program :=
  { operations
    nodes :=
      #[instruction 0,
        instruction 1,
        instruction 2,
        instruction 3 [node 1],
        instruction 4 [node 2, node 0],
        instruction 5 [node 0, node 4],
        instruction 4 [node 0, node 2],
        instruction 5 [node 0, node 6],
        instruction 5 [node 1, node 4]] }

def factDomain : FactDomain Fact where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

def limits : Limits :=
  { maxOperations := 16
    maxNodes := 32
    maxRules := 8
    maxArity := 4
    maxApplications := 32
    maxQueueEntries := 64
    maxActions := 32
    maxAcceptedFacts := 32
    maxRetainedSuggestions := 16
    maxEffort := 8
    maxObservationValue := 128
    maxDiagnosticValue := 128
    maxOutcomeCandidates := 4
    maxOutcomeSuggestions := 4
    maxProposalItems := 8
    maxInstances := 8
    maxGeneration := 4
    maxNodeDepth := 16
    maxEqualities := 8
    splitEndpointLimit :=
      { maxEndpointHeight := 32, maxAlignmentShift := 16 } }

def appendRule : Registration :=
  { key := appendKey
    head := seedOp
    kind := .instantiate
    watches := []
    writes := [] }

def centeredRule : Registration :=
  { key := centeredKey
    head := mulOp
    kind := .instantiate
    watches := []
    writes := [] }

structure Binding where
  anchor : NodeId
  input : NodeId
  complement : NodeId
  one : NodeId
  deriving DecidableEq, Repr

/-- Registry-owned interpretation of the opaque nested shape. -/
def centeredBinding? (request : RuleRequest Fact) : Option Binding := do
  if request.program.programVersion != request.action.programVersion then none else pure ()
  let product <- request.program.node? request.action.node
  let productKey <- request.program.operationKey? request.action.node
  if productKey != mulOp then none else pure ()
  let [input, complement] := product.args | none
  let difference <- request.program.node? complement
  let differenceKey <- request.program.operationKey? complement
  if differenceKey != subOp then none else pure ()
  let [one, repeated] := difference.args | none
  if repeated != input then none else pure ()
  let oneKey <- request.program.operationKey? one
  if oneKey != oneOp then none else pure ()
  pure { anchor := request.action.node, input, complement, one }

def centeredProposal? (_request : RuleRequest Fact) (binding : Binding) :
    Option InstantiationRequest := do
  let triggers := [binding.anchor, binding.input, binding.complement, binding.one]
  pure
    { key := 101
      triggers
      nodes :=
        [{ domain
           op := { index := 6 }
           args := [.existing binding.input] }]
      equalities :=
        [{ left := .existing binding.anchor
           right := .proposed 0
           payload := { index := 103 } }]
      payload := { index := 107 } }

/-- A separate opaque seed rule appends `y * (one - y)`.  This lets the same
matcher run once more against a program-version-one snapshot. -/
def appendProposal? (request : RuleRequest Fact) : Option InstantiationRequest := do
  let seed <- request.program.node? request.action.node
  let seedKey <- request.program.operationKey? request.action.node
  if seedKey != seedOp then none else pure ()
  let [input] := seed.args | none
  let one := node 2
  if request.program.operationKey? one != some oneOp then none else pure ()
  pure
    { key := 109
      triggers := [request.action.node, input, one]
      nodes :=
        [{ domain
           op := { index := 4 }
           args := [.existing one, .existing input] },
          { domain
            op := { index := 5 }
            args := [.existing input, .proposed 0] }]
      equalities := []
      payload := { index := 113 } }

structure Visit where
  programVersion : Nat
  actionVersion : Nat
  anchor : NodeId
  declaredFacts : Nat
  input : Option NodeId
  anchorGeneration : Option Nat
  deriving DecidableEq, Repr

def invoke (visits : List Visit) (request : RuleRequest Fact) :
    Outcome Fact × List Visit :=
  if request.action.key == appendKey then
    match appendProposal? request with
    | some proposal => (.success [] [.instantiate proposal] {}, visits)
    | none => (.inapplicable, visits)
  else if request.action.key == centeredKey then
    let binding := centeredBinding? request
    let visit : Visit :=
      { programVersion := request.program.programVersion
        actionVersion := request.action.programVersion
        anchor := request.action.node
        declaredFacts := request.inputs.length
        input := binding.map (fun value => value.input)
        anchorGeneration := request.program.generation? request.action.node }
    let visits := visits ++ [visit]
    match binding >>= centeredProposal? request with
    | some proposal => (.success [] [.instantiate proposal] {}, visits)
    | none => (.inapplicable, visits)
  else
    (.failed 1, visits)

def start? : Option (Engine Fact) :=
  match Engine.start factDomain program #[appendRule, centeredRule]
      (Array.replicate program.nodes.size 0) limits with
  | .ok state => some state
  | .error _ => none

def initial? : Option (RunResult Fact (List Visit)) := do
  let state <- start?
  pure (drive invoke 16 state [])

def afterAppend? : Option (RunResult Fact (List Visit)) := do
  let initial <- initial?
  match initial.state.admitInstantiation (suggestion 0) with
  | .admitted [difference, product] state =>
      if difference == node 9 && product == node 10 then
        some (drive invoke 8 state initial.cache)
      else
        none
  | _ => none

def exactCenteredSuggestion (state : Engine Fact) (index version : Nat)
    (anchor input complement one : NodeId) : Bool :=
  match state.suggestions[index]? with
  | some { action, suggestion := .instantiate request, .. } =>
      action.key == centeredKey && action.programVersion == version &&
        action.node == anchor && action.inputs.isEmpty &&
        request.key == 101 &&
        request.triggers == [anchor, input, complement, one] &&
        match request.nodes, request.equalities with
        | [product], [equality] =>
            product.domain == domain && product.op == { index := 6 } &&
              product.args == [.existing input] &&
              equality.left == .existing anchor && equality.right == .proposed 0
        | _, _ => false
  | _ => false

#guard program.check

-- The two near misses have the same `mul` head but fail the nested binding:
-- node 7 subtracts in the wrong order, while node 8 repeats the wrong source.
#guard
  match initial? with
  | some result =>
      result.stop == .saturated && result.state.metrics.requests == 4 &&
        result.state.metrics.ruleInapplicable == 2 &&
        result.state.suggestions.size == 2 &&
        result.cache ==
          [{ programVersion := 0, actionVersion := 0, anchor := node 5,
             declaredFacts := 0, input := some (node 0), anchorGeneration := some 0 },
           { programVersion := 0, actionVersion := 0, anchor := node 7,
             declaredFacts := 0, input := none, anchorGeneration := some 0 },
           { programVersion := 0, actionVersion := 0, anchor := node 8,
             declaredFacts := 0, input := none, anchorGeneration := some 0 }] &&
        exactCenteredSuggestion result.state 1 0 (node 5) (node 0) (node 4) (node 2)
  | none => false

-- Appending two nodes recompiles one new `mul` application.  Its request sees
-- exactly version 1, binds the newly assigned IDs, and still sees no facts.
#guard
  match afterAppend? with
  | some result =>
      result.stop == .saturated && result.state.programVersion == 1 &&
        result.state.program.nodes.size == 11 && result.state.applications.size == 5 &&
        result.state.suggestions.size == 3 &&
        result.cache.getLast? ==
          some
            { programVersion := 1, actionVersion := 1, anchor := node 10,
              declaredFacts := 0, input := some (node 1), anchorGeneration := some 1 } &&
        exactCenteredSuggestion result.state 2 1 (node 10) (node 1) (node 9) (node 2)
  | none => false

-- Append-only growth does not stale an otherwise fresh action.  Both the old
-- match and the newly discovered match are re-resolved against the current
-- program, then commit their exact node IDs and independently inferred depths.
#guard
  match afterAppend? with
  | some result =>
      match result.state.admitInstantiation (suggestion 1) with
      | .admitted [oldCentered] state =>
          oldCentered == node 11 && state.programVersion == 2 &&
            state.program.nodes.size == 12 && state.generations[11]? == some 1 &&
            match state.program.node? oldCentered, state.equalities[0]? with
            | some oldInstruction, some oldEquality =>
                oldInstruction.op == { index := 6 } &&
                  oldInstruction.args == [node 0] &&
                  oldEquality.left == node 5 && oldEquality.right == node 11 &&
                  match state.admitInstantiation (suggestion 2) with
                  | .admitted [newCentered] final =>
                      newCentered == node 12 && final.programVersion == 3 &&
                        final.program.nodes.size == 13 &&
                        final.generations[12]? == some 2 &&
                        match final.program.node? newCentered, final.equalities[1]? with
                        | some newInstruction, some newEquality =>
                            newInstruction.op == { index := 6 } &&
                              newInstruction.args == [node 1] &&
                              newEquality.left == node 10 &&
                              newEquality.right == node 12
                        | _, _ => false
                  | _ => false
            | _, _ => false
      | _ => false
  | none => false

end Hex.Interval.StructureViewConformance
